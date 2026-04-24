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

open Set

namespace LeanTopology
namespace TopologicalSpaceArticle

universe u v

/-!
Definition 1.1 introduces a topology on a set as a family of subsets satisfying
the three open-set axioms.
-/

/-- Definition 1.1: the open-set axioms for a family of subsets of `X`. -/
structure IsTopology_1_1 (X : Type u) (𝒪 : Set (Set X)) : Prop where
  O1_empty : (∅ : Set X) ∈ 𝒪
  O1_univ : (univ : Set X) ∈ 𝒪
  O2_inter : ∀ ⦃U V : Set X⦄, U ∈ 𝒪 -> V ∈ 𝒪 -> U ∩ V ∈ 𝒪
  O3_iUnion : ∀ {ι : Type v} (U : ι → Set X), (∀ i, U i ∈ 𝒪) -> (⋃ i, U i) ∈ 𝒪

theorem IsTopology_1_1.O2_inter' {X : Type u} {𝒪 : Set (Set X)} (h𝒪 : IsTopology_1_1 X 𝒪)
    (S : Finset (Set X)) :
    (∀ U ∈ S, U ∈ 𝒪) → ⋂₀ (↑S : Set (Set X)) ∈ 𝒪 := by
  intro hS
  induction S using Finset.induction_on with
  | empty =>
      simpa using h𝒪.O1_univ
  | @insert U S hU ih =>
      have hUO : U ∈ 𝒪 := hS U (by simp)
      have hSO : ∀ V ∈ S, V ∈ 𝒪 := by
        intro V hV
        exact hS V (by simp [hV])
      have hi : ⋂₀ ((↑S : Set (Set X))) ∈ 𝒪 := ih hSO
      simpa [Finset.coe_insert, hU] using h𝒪.O2_inter hUO hi

/-!
Definition 1.2 introduces closed sets as complements of open sets.
-/

/-- Definition 1.2: a subset is closed when its complement is open. -/
def IsClosed_1_2 {X : Type u} (𝒪 : Set (Set X)) (F : Set X) : Prop :=
  Fᶜ ∈ 𝒪

/-- Proposition 1.3: the closed-set axioms for a family of subsets of `X`. -/
structure IsClosedFamily_1_3 (X : Type u) (ℱ : Set (Set X)) : Prop where
  C1_empty : (∅ : Set X) ∈ ℱ
  C1_univ : (univ : Set X) ∈ ℱ
  C2_union : ∀ ⦃F G : Set X⦄, F ∈ ℱ → G ∈ ℱ → F ∪ G ∈ ℱ
  C3_iInter : ∀ {ι : Type v} (F : ι → Set X), (∀ i, F i ∈ ℱ) → (⋂ i, F i) ∈ ℱ

theorem IsClosedFamily_1_3.C2_union' {X : Type u} {ℱ : Set (Set X)}
  (hℱ : IsClosedFamily_1_3 X ℱ)
  (S : Finset (Set X)) :
    (∀ F ∈ S, F ∈ ℱ) → ⋃₀ (↑S : Set (Set X)) ∈ ℱ := by
      intro hS
      induction S using Finset.induction_on with
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

/-!
Proposition 1.3 becomes a certification between the article's open-set axioms
and the dual closed-set axioms for the family of complements.
-/

/-- Proposition 1.3: the open-set and closed-set formulations certify each other. -/
theorem closedSet_properties_1_3 {X : Type u} {𝒪 : Set (Set X)} :
    IsTopology_1_1 X 𝒪 <->
      IsClosedFamily_1_3 X {F : Set X | IsClosed_1_2 𝒪 F} := by
  constructor
  · intro h
    exact ⟨
      by
        simp [IsClosed_1_2]
        exact h.O1_univ,
      by
        simp [IsClosed_1_2]
        exact h.O1_empty,
      by
        simp [IsClosed_1_2]
        intro F G
        exact @h.O2_inter Fᶜ Gᶜ,
      by
        simp [IsClosed_1_2]
        intro ι F hFc
        have := @h.O3_iUnion (λ (i : ι) ↦ (F i)ᶜ)
      ,
    ⟩

/-!
Remark 1.4 explains how to interpret the intersection of zero sets inside a
fixed ambient space `X`.
-/

/-- Remark 1.4: inside a fixed space, the intersection over the empty index type is `univ`. -/
theorem iInter_empty_eq_univ_1_4 {X : Type u} :
    (⋂ i : Empty, (Empty.elim i : Set X)) = (univ : Set X) := by
  sorry

/-!
Remark 1.5 says that one may equivalently define a topology by specifying the
closed sets and asking for the dual closed-set axioms.
-/

/-- Remark 1.5: the closed-set axioms induce a topology by taking complements. -/
theorem topology_from_closed_sets_1_5 {X : Type u} {ℱ : Set (Set X)}
    (hℱ : IsClosedFamily_1_3 X ℱ) :
    IsTopology_1_1 X {U : Set X | Uᶜ ∈ ℱ} := by
  sorry

/-!
Example 1.6 introduces the discrete topology: every subset is open.
-/

/-- Example 1.6: the discrete topology family on `X`. -/
def discreteTopology_1_6 (X : Type u) : Set (Set X) :=
  univ

/-- Example 1.6: the discrete topology satisfies the open-set axioms. -/
theorem discreteTopology_isTopology_1_6 (X : Type u) :
    IsTopology_1_1 X (discreteTopology_1_6 X) := by
  sorry

/-!
Example 1.7 introduces the indiscrete topology: only `∅` and `univ` are open.
-/

/-- Example 1.7: the indiscrete topology family on `X`. -/
def indiscreteTopology_1_7 (X : Type u) : Set (Set X) :=
  {(∅ : Set X), univ}

/-- Example 1.7: the indiscrete topology satisfies the open-set axioms. -/
theorem indiscreteTopology_isTopology_1_7 (X : Type u) :
    IsTopology_1_1 X (indiscreteTopology_1_7 X) := by
  sorry

/-!
Example 1.8 introduces the finite-complement topology by first describing the
corresponding family of closed sets.
-/

/-- Example 1.8: the closed sets for the finite-complement construction. -/
def finiteClosedFamily_1_8 (X : Type u) : Set (Set X) :=
  {ℱ : Set X | ℱ = univ ∨ ℱ.Finite}

/-- Example 1.8: the corresponding finite-complement topology. -/
def finiteComplementTopology_1_8 (X : Type u) : Set (Set X) :=
  {U : Set X | U = ∅ ∨ Uᶜ.Finite}

/-- Example 1.8: the finite-complement construction gives a topology. -/
theorem finiteComplementTopology_isTopology_1_8 (X : Type u) :
    IsTopology_1_1 X (finiteComplementTopology_1_8 X) := by
  sorry

/-!
Example 1.9 reinterprets Euclidean spaces from the previous article as
topological spaces by taking the family of Euclidean-open subsets.
-/

/-- Example 1.9: the Euclidean topology family on `ℝ^n`. -/
def euclideanTopology_1_9 (n : ℕ) :
    Set (Set (EuclideanSpaceTopology.E n)) :=
  {U | EuclideanSpaceTopology.isOpenEuclidean_0_6 U}

/-- Example 1.9: the Euclidean topology satisfies the open-set axioms. -/
theorem euclideanTopology_isTopology_1_9 (n : ℕ) :
    IsTopology_1_1 (EuclideanSpaceTopology.E n) (euclideanTopology_1_9 n) := by
  sorry

/-!
Definition 1.10 compares two topologies on the same underlying set by
inclusion of their open families.
-/

/-- Definition 1.10: `𝒪₁` is coarser than `𝒪₂` when `𝒪₁ ⊆ 𝒪₂`. -/
def IsCoarser_1_10 {X : Type u} (𝒪₁ 𝒪₂ : Set (Set X)) : Prop :=
  𝒪₁ ⊆ 𝒪₂

/-- Definition 1.10: `𝒪₂` is finer than `𝒪₁` when `𝒪₁ ⊆ 𝒪₂`. -/
def IsFiner_1_10 {X : Type u} (𝒪₁ 𝒪₂ : Set (Set X)) : Prop :=
  𝒪₁ ⊆ 𝒪₂

/-!
Example 1.11 compares the standard examples: the discrete topology is the
finest, and the indiscrete topology is the coarsest.
-/

/-- Example 1.11: every topology lies between the indiscrete and discrete topologies. -/
theorem indiscrete_le_any_le_discrete_1_11 {X : Type u} {𝒪 : Set (Set X)}
    (hO : IsTopology_1_1 X 𝒪) :
    IsCoarser_1_10 (indiscreteTopology_1_7 X) 𝒪 ∧
      IsCoarser_1_10 𝒪 (discreteTopology_1_6 X) := by
  sorry

/-!
Definition 1.12 abstracts the three Euclidean distance axioms into the notion
of a distance on an arbitrary set.
-/

/-- Definition 1.12: a distance function in the sense of the article. -/
structure DistanceSpace_1_12 (X : Type u) where
  dist : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ dist x y
  D1 : ∀ x y, dist x y = 0 ↔ x = y
  D2 : ∀ x y, dist x y = dist y x
  D3 : ∀ x y z, dist x z ≤ dist x y + dist y z

/-!
Remark 1.13 restricts a distance to a nonempty subset and obtains a new
distance space.
-/

/-- Remark 1.13: the restriction of a distance to a subset is again a distance. -/
def restrictDistance_1_13 {X : Type u} (D : DistanceSpace_1_12 X) (A : Set X) :
    DistanceSpace_1_12 A := by
  refine
    { dist := fun x y => D.dist x.1 y.1
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

/-- Definition 1.14: the open ball for a distance space. -/
def openBall_1_14 {X : Type u} (D : DistanceSpace_1_12 X) (x : X) (r : ℝ) : Set X :=
  {y : X | D.dist x y < r}

/-- Definition 1.14: the closed ball for a distance space. -/
def closedBall_1_14 {X : Type u} (D : DistanceSpace_1_12 X) (x : X) (r : ℝ) : Set X :=
  {y : X | D.dist x y ≤ r}

/-!
Definition 1.15 defines open subsets of a distance space via distance balls.
-/

/-- Definition 1.15: the open sets induced by a distance. -/
def isOpenDistance_1_15 {X : Type u} (D : DistanceSpace_1_12 X) (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ r > 0, openBall_1_14 D x r ⊆ U

/-!
Proposition 1.16 states that open balls are open and closed balls are closed in
the distance-induced sense.
-/

/-- Proposition 1.16: open balls are open and closed balls are closed. -/
theorem openBall_open_closedBall_closed_1_16 {X : Type u} (D : DistanceSpace_1_12 X)
    (x : X) (r : ℝ) :
    isOpenDistance_1_15 D (openBall_1_14 D x r) ∧
      IsClosed_1_2 {U : Set X | isOpenDistance_1_15 D U} (closedBall_1_14 D x r) := by
  sorry

/-!
Proposition 1.17 says that the family of distance-open sets is a topology.
-/

/-- Proposition 1.17: the topology induced by a distance space. -/
def inducedTopology_1_17 {X : Type u} (D : DistanceSpace_1_12 X) : Set (Set X) :=
  {U : Set X | isOpenDistance_1_15 D U}

/-- Proposition 1.17: the distance-induced open sets satisfy the topology axioms. -/
theorem inducedTopology_isTopology_1_17 {X : Type u} (D : DistanceSpace_1_12 X) :
    IsTopology_1_1 X (inducedTopology_1_17 D) := by
  sorry

/-!
Definition 1.18 introduces metrizability: a topology is metrizable when it is
equal to one induced by some distance.
-/

/-- Definition 1.18: a topology is metrizable if it is induced by some distance. -/
def IsMetrizable_1_18 {X : Type u} (𝒪 : Set (Set X)) : Prop :=
  ∃ D : DistanceSpace_1_12 X, inducedTopology_1_17 D = 𝒪

/-!
Remark 1.19 emphasizes the difference between a distance space and a metrizable
space: the latter remembers only the topology, not a chosen distance.
-/

/-- Remark 1.19: a chosen distance produces a metrizable topology. -/
theorem distanceSpace_gives_metrizableSpace_1_19 {X : Type u} (D : DistanceSpace_1_12 X) :
    IsMetrizable_1_18 (inducedTopology_1_17 D) := by
  exact ⟨D, rfl⟩

/-!
Example 1.20 metrizes the discrete topology by the usual `0/1` distance.
-/

/-- Example 1.20: the discrete distance on an arbitrary set. -/
noncomputable def discreteDistance_1_20 {X : Type u} : X → X → ℝ := by
  classical
  exact fun x y ↦ if x = y then 0 else 1

/-- Example 1.20: the discrete distance satisfies the distance axioms. -/
def discreteDistanceSpace_1_20 (X : Type u) : DistanceSpace_1_12 X := by
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

/-- Example 1.20: the discrete topology is metrizable. -/
theorem discreteTopology_isMetrizable_1_20 (X : Type u) :
    IsMetrizable_1_18 (discreteTopology_1_6 X) := by
  sorry

/-!
The final statements certify that the article's set-family viewpoint agrees
with mathlib's bundled notions when one chooses to pass to them.
-/

/-- Certification: an article topology family yields a mathlib `TopologicalSpace`. -/
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

/-- Certification: the open family of a mathlib topology satisfies the article axioms. -/
theorem fromMathlibTopologicalSpace_cert {X : Type u} (T : TopologicalSpace X) :
    IsTopology_1_1 X {U : Set X | @IsOpen X T U} := by
  classical
  refine
    { O1_empty := isOpen_empty
      O1_univ := isOpen_univ
      O2_inter := by
        intro U V hU hV
        exact hU.inter hV
      O3_iUnion := by
        intro ι U hU
        exact isOpen_iUnion hU }

/-- Certification: the article's Euclidean topology agrees with the mathlib topology. -/
theorem euclideanTopology_iff_mathlibOpen_cert (n : ℕ) (U : Set (EuclideanSpaceTopology.E n)) :
    U ∈ euclideanTopology_1_9 n ↔ IsOpen U := by
  change EuclideanSpaceTopology.isOpenEuclidean_0_6 U ↔ IsOpen U
  exact EuclideanSpaceTopology.isOpenEuclidean_iff_isOpen_0_6 U

/-- Certification: the distance-induced topology yields a mathlib topological space. -/
abbrev inducedMathlibTopologicalSpace_cert {X : Type u} (D : DistanceSpace_1_12 X) :
    TopologicalSpace X :=
  toMathlibTopologicalSpace_cert (inducedTopology_1_17 D) (inducedTopology_isTopology_1_17 D)

end TopologicalSpaceArticle
end LeanTopology
