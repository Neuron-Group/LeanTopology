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

/-- Parsed data for `fin_choose`. -/
private structure FinChooseData where
  subtypeTy : Expr
  binderName : Name
  witnessPred : Expr

/-- Extract the subtype domain from a term of the form `∀ x, p x → ∃ y, q x y`. -/
private def mkFinChooseData (stx : Syntax) (type : Expr) : MetaM FinChooseData := do
  forallTelescopeReducing type fun xs body => do
    unless xs.size = 2 do
      throwErrorAt stx
        "`fin_choose` expects a term of the form `∀ x, p x → ∃ y, q x y`"
    let x := xs[0]!
    let hx := xs[1]!
    let predTy ← inferType hx
    unless ← isProp predTy do
      throwErrorAt stx
        "`fin_choose` expects the second binder to be a proposition, such as `x ∈ s`"
    let body ← whnf body
    body.withApp fun fn args => do
      match fn, args with
      | .const ``Exists _, #[_, p] =>
          let α ← inferType x
          let pred := ← mkLambdaFVars #[x] predTy
          let witnessPred := ← mkLambdaFVars #[x, hx] p
          let xDecl ← x.fvarId!.getDecl
          let xName := xDecl.userName
          let binderName := if xName == `_ then `z else xName
          let .sort u ← whnf (← inferType α)
            | throwErrorAt stx "`fin_choose` could not infer the universe of the index type"
          pure {
            subtypeTy := mkApp2 (mkConst ``Subtype [u]) α pred
            binderName := binderName
            witnessPred := witnessPred
          }
      | _, _ =>
          throwErrorAt stx
            "`fin_choose` expects a term of the form `∀ x, p x → ∃ y, q x y`"

/-- Add the constructive witness function and its specification to the local context. -/
private def elabFinChoose (goal : MVarId) (fName hfName : Syntax) (h : Expr) :
    TermElabM MVarId := goal.withContext do
  let hType ← inferType h
  let data ← mkFinChooseData fName hType

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

end

end LeanTopology
