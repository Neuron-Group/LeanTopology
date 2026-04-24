import LeanTopology.EuclideanSpaceTopology
import Mathlib.Topology.MetricSpace.Basic

/-!
# 拓扑学入门1: 拓扑空间

This file follows the article "拓扑学入门1——拓扑空间".
It records the listed definitions, examples, remarks, and propositions as Lean
skeleta, keeping the primary definitions close to the article and postponing
mathlib compatibility statements to the final section.
-/

noncomputable section

open Set LeanTopology.EuclideanSpaceTopology

namespace LeanTopology
namespace TopologicalSpaceArticle

universe u v

/-!
Definition 1.1 introduces a topology on a set as a family of subsets satisfying
the three open-set axioms.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.1: the open-set axioms for a family of subsets of `X`. -/
structure IsTopology_1_1 (X : Type u) (𝒪 : Set (Set X)) : Prop where
  O1_empty : (∅ : Set X) ∈ 𝒪
  O1_univ : (univ : Set X) ∈ 𝒪
  O2_inter : ∀ ⦃U V : Set X⦄, U ∈ 𝒪 -> V ∈ 𝒪 -> U ∩ V ∈ 𝒪
  O3_sUnion : ∀ 𝒮 : Set (Set X), (∀ U ∈ 𝒮, U ∈ 𝒪) -> ⋃₀ 𝒮 ∈ 𝒪

theorem IsTopology_1_1.O2_inter' {X : Type u} {𝒪 : Set (Set X)} (h𝒪 : IsTopology_1_1 X 𝒪)
    (𝒮 : Finset (Set X)) :
    (∀ U ∈ 𝒮, U ∈ 𝒪) → ⋂₀ (↑𝒮 : Set (Set X)) ∈ 𝒪 := by
  intro hS
  induction 𝒮 using Finset.induction_on with
  | empty =>
      simpa using h𝒪.O1_univ
  | @insert U S hU ih =>
      have hUO : U ∈ 𝒪 := hS U (by simp)
      have hSO : ∀ V ∈ S, V ∈ 𝒪 := by
        intro V hV
        exact hS V (by simp [hV])
      have hi : ⋂₀ ((↑S : Set (Set X))) ∈ 𝒪 := ih hSO
      simpa [Finset.coe_insert, hU] using h𝒪.O2_inter hUO hi

theorem IsTopology_1_1.O3_iUnion {X : Type u} {𝒪 : Set (Set X)} (h𝒪 : IsTopology_1_1 X 𝒪)
    {ι : Type*} (U : ι → Set X) :
    (∀ i, U i ∈ 𝒪) → (⋃ i, U i) ∈ 𝒪 := by
  intro hU
  let S : Set (Set X) := Set.range U
  have hS : ∀ V ∈ S, V ∈ 𝒪 := by
    intro V hV
    rcases hV with ⟨i, rfl⟩
    exact hU i
  simpa [S, Set.sUnion_range] using h𝒪.O3_sUnion S hS

/-!
Definition 1.2 introduces closed sets as complements of open sets.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.2: a subset is closed when its complement is open. -/
def IsClosed_1_2 {X : Type u} (𝒪 : Set (Set X)) (F : Set X) : Prop :=
  Fᶜ ∈ 𝒪

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 1.3: the closed-set axioms for a family of subsets of `X`. -/
structure IsClosedFamily_1_3 (X : Type u) (ℱ : Set (Set X)) : Prop where
  C1_empty : (∅ : Set X) ∈ ℱ
  C1_univ : (univ : Set X) ∈ ℱ
  C2_union : ∀ ⦃F G : Set X⦄, F ∈ ℱ → G ∈ ℱ → F ∪ G ∈ ℱ
  C3_sInter : ∀ 𝒮 : Set (Set X), (∀ F ∈ 𝒮, F ∈ ℱ) → ⋂₀ 𝒮 ∈ ℱ

theorem IsClosedFamily_1_3.C2_union' {X : Type u} {ℱ : Set (Set X)}
  (hℱ : IsClosedFamily_1_3 X ℱ)
  (𝒮 : Finset (Set X)) :
    (∀ F ∈ 𝒮, F ∈ ℱ) → ⋃₀ (↑𝒮 : Set (Set X)) ∈ ℱ := by
      intro hS
      induction 𝒮 using Finset.induction_on with
      | empty =>
        simpa using hℱ.C1_empty
      | @insert F S hF ih =>
        have hFF : F ∈ ℱ := hS F (by simp)
        have hSF : ∀ F' ∈ S, F' ∈ ℱ := by
          intro F' hF'
          exact hS F' (by simp [hF'])
        have hi : ⋃₀ ((↑S : Set (Set X))) ∈ ℱ := by
          exact ih hSF
        simpa [Finset.coe_insert, hF] using hℱ.C2_union hFF hi

theorem IsClosedFamily_1_3.C3_iInter {X : Type u} {ℱ : Set (Set X)}
    (hℱ : IsClosedFamily_1_3 X ℱ) {ι : Type*} (F : ι → Set X) :
    (∀ i, F i ∈ ℱ) → (⋂ i, F i) ∈ ℱ := by
  intro hF
  let S : Set (Set X) := Set.range F
  have hS : ∀ V ∈ S, V ∈ ℱ := by
    intro V hV
    rcases hV with ⟨i, rfl⟩
    exact hF i
  simpa [S, Set.sInter_range] using hℱ.C3_sInter S hS

/-!
Proposition 1.3 becomes a certification between the article's open-set axioms
and the dual closed-set axioms for the family of complements.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 1.3: the open-set and closed-set formulations certify each other. -/
theorem closedSet_properties_1_3 {X : Type u} {𝒪 : Set (Set X)} :
    IsTopology_1_1 X 𝒪 <->
      IsClosedFamily_1_3 X {F : Set X | IsClosed_1_2 𝒪 F} := ⟨
        λ h ↦ ⟨
          by
            simp only [IsClosed_1_2, mem_setOf_eq, compl_empty]
            exact h.O1_univ,
          by
            simp only [IsClosed_1_2, mem_setOf_eq, compl_univ]
            exact h.O1_empty,
          by
            simp only [IsClosed_1_2, mem_setOf_eq, compl_union]
            intro F G
            exact @h.O2_inter Fᶜ Gᶜ,
          by
            simp only [IsClosed_1_2, mem_setOf_eq]
            intro 𝒮 h𝒮
            set 𝒮' : Set (Set X) := {S | Sᶜ ∈ 𝒮}
              with 𝒮'df
            simp only [sInter_eq_compl_sUnion_compl, sUnion_image,
              compl_iUnion, compl_compl, compl_iInter]
            have : ⋃ F ∈ 𝒮, Fᶜ = ⋃₀ 𝒮' := by
              rw [𝒮'df]
              ext x
              simp only [
                mem_iUnion, mem_compl_iff,
                exists_prop, mem_sUnion, mem_setOf_eq
              ]; constructor
              <;> rintro ⟨F, hF⟩
              <;> use Fᶜ
              <;> simp [hF]
            rw [this]
            exact h.O3_sUnion 𝒮' (by
              simp only [𝒮'df, mem_setOf_eq]; intro S hS;
              simpa using h𝒮 Sᶜ hS
            )
          ,
        ⟩,
        λ h ↦ ⟨
          by
            have := h.C1_univ
            simp only [IsClosed_1_2, mem_setOf_eq, compl_univ] at this
            exact this,
          by
            have := h.C1_empty
            simp only [IsClosed_1_2, mem_setOf_eq, compl_empty] at this
            exact this,
          by
            intro U V
            have := @h.C2_union Uᶜ Vᶜ
            simp only [IsClosed_1_2, mem_setOf_eq, compl_compl, compl_union] at this
            exact this,
          by
            intro 𝒮 h𝒮
            set 𝒮' : Set (Set X) := {F | Fᶜ ∈ 𝒮}
              with 𝒮'df
            rw [sUnion_eq_compl_sInter_compl]
            have : ⋂₀ (compl '' 𝒮) = ⋂₀ 𝒮' := by
              rw [𝒮'df]
              ext x; constructor
              <;> simp only [sInter_image, mem_iInter,
                mem_compl_iff, mem_sInter, mem_setOf_eq]
              <;> intro h F hF
              · have := h _ hF
                simpa using this
              · have := h Fᶜ (by simpa using hF)
                simpa using this
            rw [this]
            have h𝒮' : ∀ F ∈ 𝒮', Fᶜ ∈ 𝒪 := by
              simp only [𝒮'df, mem_setOf_eq]
              intro F
              exact h𝒮 Fᶜ
            have := h.C3_sInter 𝒮'
            simp only [IsClosed_1_2, mem_setOf_eq] at this
            exact this h𝒮',
        ⟩
      ⟩

/-!
Remark 1.4 explains how to interpret the intersection of zero sets inside a
fixed ambient space `X`.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 1.4: inside a fixed space, the intersection over the empty index type is `univ`. -/
theorem iInter_empty_eq_univ_1_4 {X : Type u} :
    (⋂ i : Empty, (Empty.elim i : Set X)) = (univ : Set X) := by
  exact iInter_of_empty Empty.elim

/-!
Remark 1.5 says that one may equivalently define a topology by specifying the
closed sets and asking for the dual closed-set axioms.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 1.5: the closed-set axioms induce a topology by taking complements. -/
theorem topology_from_closed_sets_1_5 {X : Type u} {ℱ : Set (Set X)}
    (hℱ : IsClosedFamily_1_3 X ℱ) :
    IsTopology_1_1 X {U : Set X | Uᶜ ∈ ℱ} :=
  ⟨
    by
      simp only [mem_setOf_eq, compl_empty]
      exact hℱ.C1_univ,
    by
      simp only [mem_setOf_eq, compl_univ]
      exact hℱ.C1_empty,
    by
      simp only [mem_setOf_eq]
      intro U V
      rw [
        inter_eq_compl_compl_union_compl,
        compl_compl,
      ]
      exact @hℱ.C2_union Uᶜ Vᶜ,
    by
      simp only [mem_setOf_eq]; intro 𝒮 h𝒮
      simp only [sUnion_eq_compl_sInter_compl, sInter_image,
        compl_iInter, compl_compl, compl_iUnion]
      set 𝒮' := {F | Fᶜ ∈ 𝒮} with 𝒮'df
      have h𝒮' : ∀ F ∈ 𝒮', F ∈ ℱ := by
        simp only [𝒮'df, mem_setOf_eq]; intro F;
        simpa using h𝒮 Fᶜ
      have := hℱ.C3_sInter 𝒮' h𝒮'
      have eq : ⋂₀ 𝒮' = ⋂ a ∈ 𝒮, aᶜ := by
        simp only [𝒮'df]
        ext x; simp only [mem_sInter, mem_setOf_eq,
          mem_iInter, mem_compl_iff];
        constructor
        · intro h S hS
          specialize h Sᶜ
          simp only [compl_compl, mem_compl_iff] at h
          exact h hS
        · intro h F hF
          specialize h Fᶜ hF
          simpa using h
      rw [← eq]
      exact this,
  ⟩

/-!
Example 1.6 introduces the discrete topology: every subset is open.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.6: the discrete topology family on `X`. -/
def discreteTopology_1_6 (X : Type u) : Set (Set X) :=
  univ

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.6: the discrete topology satisfies the open-set axioms. -/
theorem discreteTopology_isTopology_1_6 (X : Type u) :
    IsTopology_1_1 X (discreteTopology_1_6 X) := by
  unfold discreteTopology_1_6
  exact ⟨
    by simp,
    by simp,
    by simp,
    by simp,
  ⟩

/-!
Example 1.7 introduces the indiscrete topology: only `∅` and `univ` are open.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.7: the indiscrete topology family on `X`. -/
def indiscreteTopology_1_7 (X : Type u) : Set (Set X) :=
  {(∅ : Set X), univ}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.7: the indiscrete topology satisfies the open-set axioms. -/
theorem indiscreteTopology_isTopology_1_7 (X : Type u) :
    IsTopology_1_1 X (indiscreteTopology_1_7 X) := by
  unfold indiscreteTopology_1_7
  exact ⟨
    by simp,
    by simp,
    by
      simp only [mem_insert_iff, mem_singleton_iff]
      intro U V Ueq Veq
      rcases Ueq with Ueq | Ueq
      <;> rcases Veq with Veq | Veq
      <;> simp [Ueq, Veq],
    by
      intro 𝒮 h
      grind,
  ⟩

/-!
Example 1.8 introduces the finite-complement topology by first describing the
corresponding family of closed sets.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.8: the closed sets for the finite-complement construction. -/
def finiteClosedFamily_1_8 (X : Type u) : Set (Set X) :=
  {F : Set X | F = univ ∨ F.Finite}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.8: the corresponding finite-complement topology. -/
def finiteComplementTopology_1_8 (X : Type u) : Set (Set X) :=
  {U : Set X | U = ∅ ∨ Uᶜ.Finite}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.8: the finite-complement construction gives a topology. -/
theorem finiteComplementTopology_isTopology_1_8 (X : Type u) :
    IsTopology_1_1 X (finiteComplementTopology_1_8 X) := by
  unfold finiteComplementTopology_1_8
  exact ⟨
    by simp,
    by simp,
    by
      simp only [mem_setOf_eq]; intro U V Ueq Veq;
      nth_rw 2 [inter_eq_compl_compl_union_compl]
      rw [compl_compl, finite_union]
      grind,
    by
      simp only [mem_setOf_eq, sUnion_eq_empty]
      intro 𝒮 h𝒮
      by_cases hAllEmpty : ∀ U ∈ 𝒮, U = (∅ : Set X)
      · exact Or.inl hAllEmpty
      · right
        have hNonemptyMember : ∃ U ∈ 𝒮, U ≠ (∅ : Set X) := by
          by_contra h
          exact hAllEmpty (by
            intro U hU
            by_contra hU'
            exact h ⟨U, hU, hU'⟩)
        rcases hNonemptyMember with ⟨U, hU𝒮, hUne⟩
        rcases h𝒮 U hU𝒮 with hUe | hUf
        · exact (hUne hUe).elim
        · have hsubset : (⋃₀ 𝒮)ᶜ ⊆ Uᶜ := by
            exact compl_subset_compl.mpr (subset_sUnion_of_mem hU𝒮)
          exact hUf.subset hsubset
    ,
  ⟩

/-!
Example 1.9 reinterprets Euclidean spaces from the previous article as
topological spaces by taking the family of Euclidean-open subsets.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.9: the Euclidean topology family on `ℝ^n`. -/
def euclideanTopology_1_9 (n : ℕ) :
    Set (Set (E n)) :=
  {U | isOpenEuclidean_0_6 U}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.9: the Euclidean topology satisfies the open-set axioms. -/
theorem euclideanTopology_isTopology_1_9 (n : ℕ) :
    IsTopology_1_1 (E n) (euclideanTopology_1_9 n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [euclideanTopology_1_9] using isOpen_empty_univ_0_8.left
  · simpa [euclideanTopology_1_9] using isOpen_empty_univ_0_8.right
  · intro U V hU hV
    simpa [euclideanTopology_1_9] using isOpen_inter_0_8 hU hV
  · intro S hS
    let U : S → Set (E n) := λ s ↦ s.1
    have hU : ∀ s, isOpenEuclidean_0_6 (U s) := by
      intro s
      exact hS s.1 s.2
    simpa [euclideanTopology_1_9, U, Set.sUnion_eq_iUnion] using
      isOpen_iUnion_0_8 hU

/-!
Definition 1.10 compares two topologies on the same underlying set by
inclusion of their open families.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.10: `𝒪₁` is coarser than `𝒪₂` when `𝒪₁ ⊆ 𝒪₂`. -/
def IsCoarser_1_10 {X : Type u} (𝒪₁ 𝒪₂ : Set (Set X)) : Prop :=
  𝒪₁ ⊆ 𝒪₂

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.10: `𝒪₂` is finer than `𝒪₁` when `𝒪₁ ⊆ 𝒪₂`. -/
def IsFiner_1_10 {X : Type u} (𝒪₁ 𝒪₂ : Set (Set X)) : Prop :=
  𝒪₁ ⊆ 𝒪₂

/-!
Example 1.11 compares the standard examples: the discrete topology is the
finest, and the indiscrete topology is the coarsest.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.11: every topology lies between the indiscrete and discrete topologies. -/
theorem indiscrete_le_any_le_discrete_1_11 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) :
    IsCoarser_1_10 (indiscreteTopology_1_7 X) 𝒪 ∧
      IsCoarser_1_10 𝒪 (discreteTopology_1_6 X) := by
  simp only [
    IsCoarser_1_10,
    indiscreteTopology_1_7,
    discreteTopology_1_6,
    subset_univ, and_true
  ]
  refine pair_subset h𝒪.O1_empty h𝒪.O1_univ

/-!
Definition 1.12 abstracts the three Euclidean distance axioms into the notion
of a distance on an arbitrary set.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.12: a distance function in the sense of the article. -/
class DistanceSpace_1_12 (X : Type u) where
  dist : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ dist x y
  D1 : ∀ x y, dist x y = 0 ↔ x = y
  D2 : ∀ x y, dist x y = dist y x
  D3 : ∀ x y z, dist x z ≤ dist x y + dist y z

/-!
Remark 1.13 restricts a distance to a nonempty subset and obtains a new
distance space.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 1.13: the restriction of a distance to a subset is again a distance. -/
abbrev restrictDistance_1_13 {X : Type u} [D : DistanceSpace_1_12 X] (A : Set X) :
    DistanceSpace_1_12 A := by
  refine
    { dist := fun x y => DistanceSpace_1_12.dist x.1 y.1
      nonneg := ?_
      D1 := ?_
      D2 := ?_
      D3 := ?_ }
  · intro x y
    exact D.nonneg x.1 y.1
  · intro x y
    constructor
    · intro h
      apply Subtype.ext
      exact (D.D1 x.1 y.1).1 h
    · intro h
      exact (D.D1 x.1 y.1).2 (Subtype.ext_iff.mp h)
  · intro x y
    exact D.D2 x.1 y.1
  · intro x y z
    exact D.D3 x.1 y.1 z.1

/-!
Definition 1.14 introduces open and closed balls in a distance space.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.14: the open ball for a distance space. -/
def openBall_1_14 {X : Type u} [DistanceSpace_1_12 X] (x : X) (r : ℝ) : Set X :=
  {y : X | DistanceSpace_1_12.dist x y < r}

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.14: the closed ball for a distance space. -/
def closedBall_1_14 {X : Type u} [DistanceSpace_1_12 X] (x : X) (r : ℝ) : Set X :=
  {y : X | DistanceSpace_1_12.dist x y ≤ r}

/-!
Definition 1.15 defines open subsets of a distance space via distance balls.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.15: the open sets induced by a distance. -/
def isOpenDistance_1_15 {X : Type u} [DistanceSpace_1_12 X] (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ r > 0, openBall_1_14 x r ⊆ U

/-!
Proposition 1.16 states that open balls are open and closed balls are closed in
the distance-induced sense.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 1.16: open balls are open and closed balls are closed. -/
theorem openBall_open_closedBall_closed_1_16 {X : Type u} [DistanceSpace_1_12 X]
    (x : X) (r : ℝ) :
    isOpenDistance_1_15 (openBall_1_14 x r) ∧
      IsClosed_1_2 {U : Set X | isOpenDistance_1_15 U} (closedBall_1_14 x r) := by
  sorry

/-!
Proposition 1.17 says that the family of distance-open sets is a topology.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 1.17: the topology induced by a distance space. -/
def inducedTopology_1_17 {X : Type u} [DistanceSpace_1_12 X] : Set (Set X) :=
  {U : Set X | isOpenDistance_1_15 U}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 1.17: the distance-induced open sets satisfy the topology axioms. -/
theorem inducedTopology_isTopology_1_17 {X : Type u} [DistanceSpace_1_12 X] :
    IsTopology_1_1 X inducedTopology_1_17 := by
  sorry

/-!
Definition 1.18 introduces metrizability: a topology is metrizable when it is
equal to one induced by some distance.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 1.18: a topology is metrizable if it is induced by some distance. -/
def IsMetrizable_1_18 {X : Type u} (𝒪 : Set (Set X)) : Prop :=
  ∃ D : DistanceSpace_1_12 X, @inducedTopology_1_17 X D = 𝒪

/-!
Remark 1.19 emphasizes the difference between a distance space and a metrizable
space: the latter remembers only the topology, not a chosen distance.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 1.19: a chosen distance produces a metrizable topology. -/
theorem distanceSpace_gives_metrizableSpace_1_19 {X : Type u} [D : DistanceSpace_1_12 X] :
    IsMetrizable_1_18 (@inducedTopology_1_17 X D) := by
  exact ⟨D, rfl⟩

/-!
Example 1.20 metrizes the discrete topology by the usual `0/1` distance.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.20: the discrete distance on an arbitrary set. -/
noncomputable def discreteDistance_1_20 {X : Type u} : X → X → ℝ := by
  classical
  exact fun x y ↦ if x = y then 0 else 1

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.20: the discrete distance satisfies the distance axioms. -/
abbrev discreteDistanceSpace_1_20 (X : Type u) : DistanceSpace_1_12 X := by
  classical
  refine
    { dist := discreteDistance_1_20
      nonneg := ?_
      D1 := ?_
      D2 := ?_
      D3 := ?_ }
  · intro x y
    by_cases h : x = y
    · simp [discreteDistance_1_20, h]
    · simp [discreteDistance_1_20, h]
  · intro x y
    by_cases h : x = y
    · simp [discreteDistance_1_20, h]
    · simp [discreteDistance_1_20, h]
  · intro x y
    by_cases h : x = y
    · simp [discreteDistance_1_20, h]
    · have h' : ¬ y = x := by simpa [eq_comm] using h
      simp [discreteDistance_1_20, h, h']
  · intro x y z
    sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 1.20: the discrete topology is metrizable. -/
theorem discreteTopology_isMetrizable_1_20 (X : Type u) :
    IsMetrizable_1_18 (discreteTopology_1_6 X) := by
  sorry

/-!
The final statements certify that the article's set-family viewpoint agrees
with mathlib's bundled notions when one chooses to pass to them.
-/

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: an article topology family yields a mathlib `TopologicalSpace`. -/
abbrev toMathlibTopologicalSpace_cert {X : Type u} (𝒪 : Set (Set X))
    (hO : IsTopology_1_1 X 𝒪) : TopologicalSpace X := by
  classical
  refine
    { IsOpen := fun U => U ∈ 𝒪
      isOpen_univ := hO.O1_univ
      isOpen_inter := by
        intro U V hU hV
        exact hO.O2_inter hU hV
      isOpen_sUnion := by
        intro S hS
        classical
        let U : S → Set X := fun s => s.1
        have hU : ∀ s, U s ∈ 𝒪 := by
          intro s
          exact hS s.1 s.2
        simpa [U, sUnion_eq_iUnion] using hO.O3_iUnion U hU }

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: the open family of a mathlib topology satisfies the article axioms. -/
theorem fromMathlibTopologicalSpace_cert {X : Type u} (T : TopologicalSpace X) :
    IsTopology_1_1 X {U : Set X | @IsOpen X T U} := by
  classical
  refine
    { O1_empty := isOpen_empty
      O1_univ := isOpen_univ
      O2_inter := by
        intro U V hU hV
        exact hU.inter hV
      O3_sUnion := by
        intro S hS
        exact isOpen_sUnion hS }

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: the article's Euclidean topology agrees with the mathlib topology. -/
theorem euclideanTopology_iff_mathlibOpen_cert (n : ℕ) (U : Set (EuclideanSpaceTopology.E n)) :
    U ∈ euclideanTopology_1_9 n ↔ IsOpen U := by
  change EuclideanSpaceTopology.isOpenEuclidean_0_6 U ↔ IsOpen U
  exact EuclideanSpaceTopology.isOpenEuclidean_iff_isOpen_0_6 U

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: the distance-induced topology yields a mathlib topological space. -/
abbrev inducedMathlibTopologicalSpace_cert {X : Type u} [DistanceSpace_1_12 X] :
    TopologicalSpace X :=
  toMathlibTopologicalSpace_cert inducedTopology_1_17 inducedTopology_isTopology_1_17

end TopologicalSpaceArticle
end LeanTopology
