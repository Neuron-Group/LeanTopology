import LeanTopology.TopologicalSpace
import Mathlib.Data.PNat.Basic

/-!
# 拓扑学入门2: 邻域、邻域基
-/

noncomputable section

open Set LeanTopology.EuclideanSpaceTopology

namespace LeanTopology
namespace NeighborhoodBasis

universe u v

section TopologyPart

open LeanTopology.TopologicalSpace

/-!
Definition 2.1 introduces neighborhoods through containment of an open set
around the chosen point.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.1: `V` is a neighborhood of `x` when it contains some open set around `x`. -/
def IsNeighborhood_2_1 {X : Type u} (𝒪 : Set (Set X)) (x : X) (V : Set X) : Prop :=
  ∃ U : Set X, U ∈ 𝒪 ∧ x ∈ U ∧ U ⊆ V

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.1: an open neighborhood is a neighborhood that is itself open. -/
def IsOpenNeighborhood_2_1 {X : Type u} (𝒪 : Set (Set X)) (x : X) (V : Set X) : Prop :=
  IsNeighborhood_2_1 𝒪 x V ∧ V ∈ 𝒪

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.1: a closed neighborhood is a neighborhood that is itself closed. -/
def IsClosedNeighborhood_2_1 {X : Type u} (𝒪 : Set (Set X)) (x : X) (V : Set X) : Prop :=
  IsNeighborhood_2_1 𝒪 x V ∧ IsClosed_1_2 𝒪 V

/-!
Proposition 2.2 identifies open neighborhoods with open sets containing the
point.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.2: an open neighborhood is exactly an open set containing the point. -/
theorem openNeighborhood_iff_2_2 {X : Type u} {𝒪 : Set (Set X)}
    (_𝒪 : IsTopology_1_1 X 𝒪) (x : X) (V : Set X) :
    IsOpenNeighborhood_2_1 𝒪 x V <-> V ∈ 𝒪 ∧ x ∈ V := by
  constructor
  · rintro ⟨hV, Vop⟩
    rcases hV with ⟨U, Uop, xinU, UsubV⟩
    exact ⟨Vop, UsubV xinU⟩
  · rintro ⟨Vop, xinV⟩
    exact ⟨⟨V, Vop, xinV, LE.le.subset λ _ a_1 ↦ a_1⟩, Vop⟩

/-!
Proposition 2.3 says that finite intersections of neighborhoods are still
neighborhoods.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.3: a finite intersection of neighborhoods is again a neighborhood. -/
theorem neighborhood_sInter_finset_2_3 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (x : X) (𝒱 : Finset (Set X)) :
    (∀ V ∈ 𝒱, IsNeighborhood_2_1 𝒪 x V) ->
      IsNeighborhood_2_1 𝒪 x (⋂₀ (↑𝒱 : Set (Set X))) := by
  intro hyp
  unfold IsNeighborhood_2_1 at hyp
  fin_choose f hf using hyp
  refine ⟨⋂₀ (↑(𝒱.attach.image f) : Set (Set X)), ?_, ?_, ?_⟩
  · exact h𝒪.O2_inter' (𝒱.attach.image f) (by
      intro U hU
      rcases Finset.mem_image.mp hU with ⟨V, hV, rfl⟩
      exact (hf V).1)
  · rw [Set.mem_sInter]
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨V, hV, rfl⟩
    exact (hf V).2.1
  · intro y hy
    rw [Set.mem_sInter] at hy ⊢
    intro V hV
    have hy' : y ∈ f ⟨V, hV⟩ := by
      apply hy
      exact Finset.mem_image.mpr ⟨⟨V, hV⟩, by simp, rfl⟩
    exact (hf ⟨V, hV⟩).2.2 hy'

/-!
Proposition 2.4 gives a neighborhood-based criterion for openness.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.4: a set is open iff each of its points has a neighborhood contained in it. -/
theorem isOpen_iff_neighborhood_2_4 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (U : Set X) :
    U ∈ 𝒪 ↔ ∀ x ∈ U, ∃ V : Set X, IsNeighborhood_2_1 𝒪 x V ∧ V ⊆ U := open Classical in by
  constructor
  · intro hU x xinU
    have UisNeib := (openNeighborhood_iff_2_2 h𝒪 _ _).mpr ⟨hU, xinU⟩
    use U; use UisNeib.left;
  · intro hyp
    choose f hf using hyp
    choose g hg using hf
    choose h hh using g
    set ι := {x : X // x ∈ U} with ιdf
    set prj : ι -> Set X
      := λ i ↦ h i.val i.property
        with prj_df
    set 𝒮 : Set (Set X) := prj '' univ
      with 𝒮df
    have : ∀ S ∈ 𝒮, S ∈ 𝒪 := by
      intro S hS
      simp only [𝒮df, prj_df, image_univ, mem_range] at hS
      rcases hS with ⟨⟨y, ay⟩, hy⟩; rw [← hy]
      exact (hh y ay).left
    set U' := ⋃₀ 𝒮 with U'df
    have hU' : U' ∈ 𝒪 := by
      rw [U'df]
      exact h𝒪.O3_sUnion 𝒮 this
    have Ueq : U = U' := by
      refine ext ?_
      intro x
      constructor
      <;> intro hx
      · simp only [U'df, 𝒮df, prj_df,
          image_univ, sUnion_range, mem_iUnion]
        use ⟨x, hx⟩;
        specialize hh x hx
        rcases hh with ⟨_, hh, _⟩
        exact hh
      · simp only [U'df, 𝒮df, prj_df, image_univ,
          sUnion_range, mem_iUnion] at hx
        rcases hx with ⟨⟨y, ay⟩, hy⟩
        rcases hh y ay with ⟨_, _, hh⟩
        specialize hg y ay
        exact hh.trans hg hy
    rw [Ueq]
    exact hU'

/-!
Definition 2.5 singles out representative neighborhoods that refine all
neighborhoods of the point.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.5: a neighborhood basis at `x`. -/
def IsNeighborhoodBasis_2_5 {X : Type u} (𝒪 : Set (Set X)) (x : X) (𝒰 : Set (Set X)) : Prop :=
  ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V → ∃ U ∈ 𝒰, U ⊆ V

/-!
Example 2.6 says that all neighborhoods of a point form a neighborhood basis.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.6: the family of all neighborhoods of `x` is a neighborhood basis. -/
theorem allNeighborhoods_isNeighborhoodBasis_2_6 {X : Type u} {𝒪 : Set (Set X)} (x : X) :
    IsNeighborhoodBasis_2_5 𝒪 x {V : Set X | IsNeighborhood_2_1 𝒪 x V} := by
  sorry

/-!
Example 2.7 says that all open neighborhoods of a point also form a
neighborhood basis.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.7: the family of all open neighborhoods of `x` is a neighborhood basis. -/
theorem allOpenNeighborhoods_isNeighborhoodBasis_2_7 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (x : X) :
    IsNeighborhoodBasis_2_5 𝒪 x {V : Set X | IsOpenNeighborhood_2_1 𝒪 x V} := by
  sorry

/-!
Example 2.8 specializes the definition to distance spaces. Open balls centered
at `x`, and even the balls of radius `1 / n`, form neighborhood bases.
-/

section DistancePart

open LeanTopology.TopologicalSpace

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.8: all open balls centered at `x` form a neighborhood basis. -/
theorem distance_openBall_isNeighborhoodBasis_2_8 {X : Type u}
    [DistanceSpace_1_12 X]
    (x : X) :
    IsNeighborhoodBasis_2_5
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) x
      {U : Set X | ∃ r : ℝ, 0 < r ∧ U = openBall_1_14 x r} := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.8: the balls of radius `1 / n` form a countable neighborhood basis. -/
theorem distance_invPNatBall_isNeighborhoodBasis_2_8 {X : Type u}
    [DistanceSpace_1_12 X]
    (x : X) :
    IsNeighborhoodBasis_2_5
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) x
      {U : Set X | ∃ n : ℕ+, U = openBall_1_14 x (1 / (n : ℝ))} := by
  sorry

/-!
Example 2.9 records the discrete-space singleton basis and the notion of an
isolated point.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.9: `x` is isolated when `{x}` is a neighborhood of `x`. -/
def IsIsolatedPoint_2_9 {X : Type u} (𝒪 : Set (Set X)) (x : X) : Prop :=
  IsNeighborhood_2_1 𝒪 x ({x} : Set X)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.9: in a discrete space, `{x}` forms a neighborhood basis at `x`. -/
theorem discrete_singleton_isNeighborhoodBasis_2_9 {X : Type u} (x : X) :
    IsNeighborhoodBasis_2_5 (discreteTopology_1_6 X) x
      ({({x} : Set X)} : Set (Set X)) := by
  sorry

/-!
Proposition 2.10 packages the characteristic properties `NB1` through `NB4` of
an assigned family of neighborhood bases.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.10: the abstract axioms `NB1`--`NB4` for pointwise neighborhood bases. -/
structure IsNeighborhoodBasisFamily_2_10 (X : Type u) (𝒰 : X → Set (Set X)) : Prop where
  NB1_nonempty : ∀ x : X, (𝒰 x).Nonempty
  NB2_mem : ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ 𝒰 x → x ∈ U
  NB3_inter : ∀ ⦃x : X⦄ ⦃U₁ U₂ : Set X⦄, U₁ ∈ 𝒰 x → U₂ ∈ 𝒰 x →
    ∃ V : Set X, V ∈ 𝒰 x ∧ V ⊆ U₁ ∩ U₂
  NB4_local : ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ 𝒰 x →
    ∃ V : Set X, V ∈ 𝒰 x ∧ ∀ y ∈ V, ∃ W : Set X, W ∈ 𝒰 y ∧ W ⊆ U

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.10: actual neighborhood bases satisfy the axioms `NB1`--`NB4`. -/
theorem neighborhoodBasis_properties_2_10 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) {𝒰 : X → Set (Set X)}
    (h𝒰 : ∀ x : X, IsNeighborhoodBasis_2_5 𝒪 x (𝒰 x)) :
    IsNeighborhoodBasisFamily_2_10 X 𝒰 := by
  sorry

/-!
Proposition 2.11 reconstructs a topology from pointwise neighborhood-basis
families satisfying `NB1` through `NB4`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.11: the open family generated by prescribed neighborhood bases. -/
def topologyFromNeighborhoodBases_2_11 {X : Type u} (𝒰 : X → Set (Set X)) : Set (Set X) :=
  {U : Set X | ∀ x ∈ U, ∃ V : Set X, V ∈ 𝒰 x ∧ V ⊆ U}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.11: neighborhood-basis axioms determine a unique topology. -/
theorem topology_from_neighborhoodBases_2_11 {X : Type u} [Nonempty X] {𝒰 : X → Set (Set X)}
    (h𝒰 : IsNeighborhoodBasisFamily_2_10 X 𝒰) :
    IsTopology_1_1 X (topologyFromNeighborhoodBases_2_11 𝒰) ∧
      (∀ x : X, IsNeighborhoodBasis_2_5 (topologyFromNeighborhoodBases_2_11 𝒰) x (𝒰 x)) ∧
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 →
        (∀ x : X, IsNeighborhoodBasis_2_5 𝒪 x (𝒰 x)) →
          𝒪 = topologyFromNeighborhoodBases_2_11 𝒰 := by
  sorry

/-!
Definition 2.12 introduces first countability.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.12: a space is first countable if each point has a countable
neighborhood basis. -/
def FirstCountable_2_12 {X : Type u} (𝒪 : Set (Set X)) : Prop :=
  ∀ x : X, ∃ 𝒰 : Set (Set X), IsNeighborhoodBasis_2_5 𝒪 x 𝒰 ∧ 𝒰.Countable

/-!
Example 2.13 records that distance spaces, discrete spaces, and metrizable
spaces are first countable.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.13: every distance space is first countable. -/
theorem distanceSpace_firstCountable_2_13 {X : Type u}
    [DistanceSpace_1_12 X] :
    FirstCountable_2_12 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.13: every discrete space is first countable. -/
theorem discreteSpace_firstCountable_2_13 {X : Type u} :
    FirstCountable_2_12 (discreteTopology_1_6 X) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.13: every metrizable space is first countable. -/
theorem metrizableSpace_firstCountable_2_13 {X : Type u} {𝒪 : Set (Set X)}
    (hM : IsMetrizable_1_18 𝒪) :
    FirstCountable_2_12 𝒪 := by
  sorry

/-!
Example 2.14 discusses first countability for the cofinite topology.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.14: a countable cofinite space is first countable. -/
theorem countable_finiteComplement_firstCountable_2_14 {X : Type u}
    (hX : Set.Countable (univ : Set X)) :
    FirstCountable_2_12 (finiteComplementTopology_1_8 X) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.14: an uncountable cofinite space is not first countable. -/
theorem uncountable_finiteComplement_not_firstCountable_2_14 {X : Type u}
    (hX : ¬ Set.Countable (univ : Set X)) :
    ¬ FirstCountable_2_12 (finiteComplementTopology_1_8 X) := by
  sorry

/-!
Proposition 2.15 refines first countability to a decreasing countable
neighborhood basis.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.15: a first-countable point admits a decreasing countable neighborhood basis. -/
theorem decreasing_neighborhoodBasis_2_15 {X : Type u} {𝒪 : Set (Set X)}
    (hFirst : FirstCountable_2_12 𝒪) (x : X) :
    ∃ V : ℕ → Set X, IsNeighborhoodBasis_2_5 𝒪 x (Set.range V) ∧
      ∀ n : ℕ, V (n + 1) ⊆ V n := by
  sorry

/-!
Definition 2.16 introduces convergence of sequences in a topological space.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.16: a sequence in `X` is a map `ℕ+ → X`. -/
abbrev Sequence_2_16 (X : Type u) := ℕ+ → X

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.16: topological convergence of a sequence to a point. -/
def TendstoSeq_2_16 {X : Type u} (𝒪 : Set (Set X)) (xₙ : Sequence_2_16 X) (x : X) : Prop :=
  ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V →
    ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n → xₙ n ∈ V

/-!
Remark 2.17 notes that sequence limits need not be unique in general.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 2.17: in the indiscrete two-point space, a constant sequence may have two limits. -/
theorem indiscrete_nonunique_limit_2_17 :
    let X := Bool
    let 𝒪 := indiscreteTopology_1_7 X
    let xₙ : Sequence_2_16 X := λ _ ↦ false
    TendstoSeq_2_16 𝒪 xₙ false ∧ TendstoSeq_2_16 𝒪 xₙ true := by
  sorry

end DistancePart
end TopologyPart

/-!
Proposition 2.18 reduces convergence to checking a neighborhood basis.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.18: convergence may be tested on a neighborhood basis. -/
theorem tendstoSeq_iff_neighborhoodBasis_2_18 {X : Type u} {𝒪 : Set (Set X)}
    (xₙ : Sequence_2_16 X) (x : X) {𝒰 : Set (Set X)}
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰) :
    TendstoSeq_2_16 𝒪 xₙ x <->
      ∀ U ∈ 𝒰, ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n -> xₙ n ∈ U := by
  sorry

/-!
Proposition 2.19 compares topological convergence in a distance space with the
usual epsilon formulation, and with convergence of the real distance sequence.
-/

section MetricConvergencePart

open LeanTopology.TopologicalSpace

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.19: epsilon-convergence of a real sequence to a real limit. -/
def RealSequenceConvergesTo_2_19 (a : ℕ+ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n -> |a n - l| < ε

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.19: the three usual formulations of metric convergence are equivalent. -/
theorem tendstoSeq_metric_2_19 {X : Type u}
    [DistanceSpace_1_12 X]
    (xₙ : Sequence_2_16 X) (x : X) :
    (TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ x <->
      ∀ ε > 0, ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n -> DistanceSpace_1_12.dist (xₙ n) x < ε) ∧
    ((∀ ε > 0, ∃ N : ℕ+, ∀ n : ℕ+, N ≤ n -> DistanceSpace_1_12.dist (xₙ n) x < ε) <->
      RealSequenceConvergesTo_2_19 (λ n : ℕ+ ↦ DistanceSpace_1_12.dist (xₙ n) x) 0) := by
  sorry

/-!
Proposition 2.20 says that metric limits are unique.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.20: a convergent sequence in a distance space has at most one limit. -/
theorem tendstoSeq_metric_limit_unique_2_20 {X : Type u}
    [DistanceSpace_1_12 X]
    (xₙ : Sequence_2_16 X) {x y : X} :
    TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ x →
      TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ y →
        x = y := by
  sorry

/-!
Before Proposition 2.21, we record the Euclidean metric on `E n` as an
instance of the distance-space structure, and then restrict it to a subset.
-/

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: Euclidean space carries the distance-space structure. -/
abbrev euclideanDistanceSpace_cert_2_21 (n : ℕ) :
    DistanceSpace_1_12 (EuclideanSpaceTopology.E n) := by
  refine
    { dist := dist
      nonneg := ?_
      D1 := ?_
      D2 := ?_
      D3 := ?_ }
  · intro x y
    exact dist_nonneg
  · intro x y
    exact dist_eq_zero
  · intro x y
    exact dist_comm x y
  · intro x y z
    exact dist_triangle x y z

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.21: the topology on a Euclidean subspace induced from the
restricted distance. -/
abbrev euclideanSubspaceTopology_2_21 (n : ℕ)
    (A : Set (EuclideanSpaceTopology.E n)) : Set (Set A) :=
  @inducedTopology_1_17 A (restrictDistance_1_13 (D := euclideanDistanceSpace_cert_2_21 n) A)

/-!
Proposition 2.21 characterizes convergence in Euclidean subspaces coordinate by
coordinate.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.21: convergence in a Euclidean subspace is equivalent to
coordinatewise convergence. -/
theorem tendstoSeq_euclideanSubspace_2_21 {n : ℕ}
    (A : Set (EuclideanSpaceTopology.E n))
    (xᵢ : Sequence_2_16 A) (x : A) :
    TendstoSeq_2_16 (euclideanSubspaceTopology_2_21 n A) xᵢ x ↔
      ∀ k : Fin n,
        RealSequenceConvergesTo_2_19 (λ i : ℕ+ ↦ (xᵢ i).1 k) (x.1 k) := by
  sorry

end MetricConvergencePart

/-!
The final statements connect the article's neighborhood language with mathlib's
neighborhood filters and convergence notions.
-/

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: neighborhood in the article sense agrees with membership in `𝓝 x`. -/
theorem isNeighborhood_iff_mem_nhds_cert {X : Type u} (T : TopologicalSpace X) (x : X) (V : Set X) :
    IsNeighborhood_2_1 {U : Set X | @IsOpen X T U} x V ↔ V ∈ nhds x := by
  sorry

/-- 𝒞ℯ𝓇𝓉𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃: topological sequence convergence matches filter convergence in mathlib. -/
theorem tendstoSeq_iff_tendsto_cert {X : Type u} (T : TopologicalSpace X)
    (xₙ : Sequence_2_16 X) (x : X) :
    TendstoSeq_2_16 {U : Set X | @IsOpen X T U} xₙ x ↔ Filter.Tendsto xₙ Filter.atTop (nhds x) := by
  sorry

end NeighborhoodBasis
end LeanTopology
