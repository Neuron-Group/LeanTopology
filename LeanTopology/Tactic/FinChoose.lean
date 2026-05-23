import LeanTopology.Basic
import Mathlib.Tactic

/-!
# `fin_choose` tactic

`fin_choose` is a constructive alternative to `choose` for hypotheses of the form
`∀ x, p x → ∃ y, q x y`. In the common `Finset` case
`h : ∀ x ∈ s, ∃ y, q x y`, it produces:

* `f  : ∀ z : {x // x ∈ s}, ...`
* `hf : ∀ z : {x // x ∈ s}, q z.1 (f z)`

This avoids `Classical.choice` by only choosing from the explicit existential proof
attached to each subtype element.
-/

open Lean Meta Elab Tactic

namespace LeanTopology
namespace FinChoose

/-- Constructive choice on a finite set, built by induction on the `Finset`. -/
theorem chooseOnFinset {α : Type u} [DecidableEq α] (s : Finset α)
    {β : α → Sort v} {p : ∀ a, β a → Prop}
    (h : ∀ a ∈ s, ∃ b, p a b) :
    ∃ f : ∀ a : {x // x ∈ s}, β a.1, ∀ a : {x // x ∈ s}, p a.1 (f a) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha' : ∃ b, p a b := h a (by simp)
      have hs : ∀ x ∈ s, ∃ b, p x b := by
        intro x hx
        exact h x (by simp [hx])
      rcases ha' with ⟨b, hb⟩
      rcases ih hs with ⟨f, hf⟩
      let g : ∀ z : {x // x ∈ insert a s}, β z.1 := by
        rintro ⟨x, hx⟩
        by_cases hxa : x = a
        · subst hxa
          exact b
        · exact f ⟨x, by simpa [Finset.mem_insert, hxa] using hx⟩
      refine ⟨g, ?_⟩
      rintro ⟨x, hx⟩
      dsimp [g]
      by_cases hxa : x = a
      · subst hxa
        simpa using hb
      · simpa [hxa] using hf ⟨x, by simpa [Finset.mem_insert, hxa] using hx⟩

/-- Constructive choice on a finite type, obtained from `Fintype.elems`. -/
theorem chooseOnFintype {α : Type u} [Fintype α]
    {β : α → Sort v} {p : ∀ a, β a → Prop}
    (h : ∀ a, ∃ b, p a b) :
    ∃ f : ∀ a, β a, ∀ a, p a (f a) := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let finDecEq : DecidableEq (Fin (Fintype.card α)) := inferInstance
  let _ : DecidableEq α := fun a b =>
    match finDecEq (e a) (e b) with
    | isTrue hab => isTrue (e.injective hab)
    | isFalse hab => isFalse (fun hab' => hab (by simpa [hab']))
  let s : Finset α := Finset.univ
  have hs : ∀ a ∈ s, ∃ b, p a b := by
    intro a _
    exact h a
  rcases chooseOnFinset s hs with ⟨f, hf⟩
  refine ⟨fun a => f ⟨a, by simp [s]⟩, ?_⟩
  intro a
  simpa [s] using hf ⟨a, by simp [s]⟩

/-- Parsed data for `fin_choose`. -/
private structure FinChooseData where
  isFintype : Bool
  domainTy : Expr
  subtypeTy : Expr
  binderName : Name
  witnessPred : Expr

/-- Parse a term of the form `∀ x, p x → ∃ y, q x y` or `∀ x, ∃ y, q x y`. -/
private def mkFinChooseData (stx : Syntax) (type : Expr) : MetaM FinChooseData := do
  let type ← whnf type
  forallTelescopeReducing type fun xs body => do
    let x := xs[0]!
    let α ← inferType x
    let xDecl ← x.fvarId!.getDecl
    let xName := xDecl.userName
    let binderName := if xName == `_ then `z else xName
    let .sort u ← whnf (← inferType α)
      | throwErrorAt stx "`fin_choose` could not infer the universe of the index type"
    if xs.size = 2 then
      let hx := xs[1]!
      let predTy ← inferType hx
      unless ← isProp predTy do
        throwErrorAt stx
          "`fin_choose` expects the second binder to be a proposition, such as `x ∈ s`"
      let body ← whnf body
      body.withApp fun fn args => do
        match fn, args with
        | .const ``Exists _, #[_, p] =>
            let pred := ← mkLambdaFVars #[x] predTy
            let witnessPred := ← mkLambdaFVars #[x, hx] p
            pure {
              isFintype := false
              domainTy := α
              subtypeTy := mkApp2 (mkConst ``Subtype [u]) α pred
              binderName := binderName
              witnessPred := witnessPred
            }
        | _, _ =>
            throwErrorAt stx
              "`fin_choose` expects a term of the form `∀ x, p x → ∃ y, q x y` or `∀ x, ∃ y, q x y`"
    else if xs.size = 1 then
      pure {
        isFintype := true
        domainTy := α
        subtypeTy := α
        binderName := binderName
        witnessPred := mkConst ``True
      }
    else
      throwErrorAt stx
        "`fin_choose` expects a term of the form `∀ x, p x → ∃ y, q x y` or `∀ x, ∃ y, q x y`"

/-- Add the constructive witness function and its specification to the local context. -/
private def elabFinChoose (goal : MVarId) (fName hfName : Syntax) (h : Expr) :
    TermElabM MVarId := goal.withContext do
  let hType ← inferType h
  let data ← mkFinChooseData fName hType

  if data.isFintype then
    let fintypeConst ← mkConstWithFreshMVarLevels ``Fintype
    let fintypeInst? ← synthInstance? (mkApp fintypeConst data.domainTy)
    unless fintypeInst?.isSome do
      throwErrorAt fName
          "`fin_choose` can handle `∀ x, ∃ y, q x y` only when the type of `x` has a `Fintype` instance"
    let choiceProof ← mkAppM ``LeanTopology.FinChoose.chooseOnFintype #[h]
    let (choiceFVarId, goal) ← (← goal.assert .anonymous (← inferType choiceProof) choiceProof).intro1P
    let #[subgoal] ← goal.cases choiceFVarId
      | throwErrorAt fName "`fin_choose` failed to destruct the constructive choice witness"
    let #[Expr.fvar fFVarId, Expr.fvar hfFVarId] ← pure subgoal.fields
      | throwErrorAt fName "`fin_choose` failed to extract the witness function and proof"
    let goal ← subgoal.mvarId.rename fFVarId fName.getId
    let goal ← goal.rename hfFVarId hfName.getId
    goal.withContext do
      Term.addLocalVarInfo fName (mkFVar fFVarId)
      Term.addLocalVarInfo hfName (mkFVar hfFVarId)
    return goal

  let (fFVarId, goal) ← goal.withContext do
    withLocalDeclD data.binderName data.subtypeTy fun z => do
      let xz := mkProj ``Subtype 0 z
      let hxz := mkProj ``Subtype 1 z
      let hz := mkAppN h #[xz, hxz]
      let fBody ← mkAppM ``Exists.choose #[hz]
      let fTy ← mkForallFVars #[z] (← inferType fBody)
      let fVal ← mkLambdaFVars #[z] fBody
      goal.note fName.getId fVal fTy

  goal.withContext do
    Term.addLocalVarInfo fName (mkFVar fFVarId)

  let (hfFVarId, goal) ← goal.withContext do
    withLocalDeclD data.binderName data.subtypeTy fun z => do
      let xz := mkProj ``Subtype 0 z
      let hxz := mkProj ``Subtype 1 z
      let hz := mkAppN h #[xz, hxz]
      let pz := mkAppN data.witnessPred #[xz, hxz]
      let f := mkFVar fFVarId
      let hfBody ← mkAppM ``Exists.choose_spec #[hz]
      let hfTy ← mkForallFVars #[z] (mkApp pz (mkApp f z))
      let hfVal ← mkLambdaFVars #[z] hfBody
      goal.note hfName.getId hfVal hfTy

  goal.withContext do
    Term.addLocalVarInfo hfName (mkFVar hfFVarId)
  pure goal

end FinChoose

/--
`fin_choose f hf using h` is a constructive variant of `choose` for a bounded hypothesis
`h : ∀ x, p x → ∃ y, q x y`.

In the common `Finset` form `h : ∀ x ∈ s, ∃ y, q x y`, it introduces:

* `f  : ∀ z : {x // x ∈ s}, ...`
* `hf : ∀ z : {x // x ∈ s}, q z.1 (f z)`

Unlike `choose`, this tactic does not rely on `Classical.choice`.
-/
syntax (name := finChoose) "fin_choose" ident ident "using" term : tactic

elab_rules : tactic
| `(tactic| fin_choose $fName:ident $hfName:ident using $h:term) => withMainContext do
    let h ← elabTerm h none
    let goal ← FinChoose.elabFinChoose (← getMainGoal) fName hfName h
    replaceMainGoal [goal]

section

example {α β : Type} (s : Finset α) (_h : ∀ x ∈ s, ∃ _ : β, x ∈ s) : True := by
  fin_choose f hf using _h
  guard_hyp f : {x // x ∈ s} → β
  guard_hyp hf : ∀ z : {x // x ∈ s}, z.1 ∈ s
  trivial

example {α : Type} (s : Finset α) (_h : ∀ x ∈ s, ∃ _ : x = x, True) : True := by
  fin_choose f hf using _h
  guard_hyp f : ∀ z : {x // x ∈ s}, z.1 = z.1
  guard_hyp hf : ∀ z : {x // x ∈ s}, True
  trivial

example {X : Type} {𝒪 : Set (Set X)} (x : X) (𝒱 : Finset (Set X))
    (_hyp : ∀ V ∈ 𝒱, ∃ U : Set X, U ∈ 𝒪 ∧ x ∈ U ∧ U ⊆ V) : True := by
  fin_choose f hf using _hyp
  guard_hyp f : ↥𝒱 → Set X
  guard_hyp hf : ∀ V : ↥𝒱, f V ∈ 𝒪 ∧ x ∈ f V ∧ f V ⊆ V.1
  trivial

example {n : ℕ} (_h : ∀ i : Fin n, ∃ y : ℚ, True) : True := by
  fin_choose f hf using _h
  guard_hyp f : Fin n → ℚ
  guard_hyp hf : ∀ i : Fin n, True
  trivial

end

end LeanTopology
