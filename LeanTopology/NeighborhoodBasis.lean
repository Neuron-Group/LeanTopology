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

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.3, consequence: the intersection of two neighborhoods is again a neighborhood. -/
theorem neighborhood_inter_2_3 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (x : X)
    (U₁ : Set X) (hU₁ : IsNeighborhood_2_1 𝒪 x U₁)
    (U₂ : Set X) (hU₂ : IsNeighborhood_2_1 𝒪 x U₂) :
      IsNeighborhood_2_1 𝒪 x (U₁ ∩ U₂) := by
  simpa [Set.sInter_pair] using
    neighborhood_sInter_finset_2_3 h𝒪 x ({U₁, U₂} : Finset (Set X)) (by
      intro V hV
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV
      rcases hV with rfl | rfl
      · exact hU₁
      · exact hU₂)

/-!
Proposition 2.4 gives a neighborhood-based criterion for openness.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.4: a set is open iff each of its points has a neighborhood contained in it. -/
theorem isOpen_iff_neighborhood_2_4 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (U : Set X) :
    U ∈ 𝒪 <-> ∀ x ∈ U, ∃ V : Set X, IsNeighborhood_2_1 𝒪 x V ∧ V ⊆ U
      := by
  constructor
  · intro hU x xinU
    exact ⟨U, ⟨U, hU, xinU, Subset.rfl⟩, Subset.rfl⟩
  · intro hyp
    let 𝒮 : Set (Set X) := {W : Set X | W ∈ 𝒪 ∧ W ⊆ U}
    have h𝒮 : ∀ W ∈ 𝒮, W ∈ 𝒪 := by
      intro W hW
      have hW' : W ∈ 𝒪 ∧ W ⊆ U := by
        simpa [𝒮] using hW
      exact hW'.1
    have hUnion : ⋃₀ 𝒮 ∈ 𝒪 := h𝒪.O3_sUnion 𝒮 h𝒮
    have hSubset : ⋃₀ 𝒮 ⊆ U := by
      intro x hx
      rcases mem_sUnion.mp hx with ⟨W, hW𝒮, hxW⟩
      have hW' : W ∈ 𝒪 ∧ W ⊆ U := by
        simpa [𝒮] using hW𝒮
      exact hW'.2 hxW
    have hSuperset : U ⊆ ⋃₀ 𝒮 := by
      intro x hx
      rcases hyp x hx with ⟨V, hVneigh, hVU⟩
      rcases hVneigh with ⟨W, hWOpen, hxW, hWV⟩
      apply mem_sUnion.mpr
      refine ⟨W, ?_, hxW⟩
      change W ∈ 𝒪 ∧ W ⊆ U
      exact ⟨hWOpen, hWV.trans hVU⟩
    have hEq : ⋃₀ 𝒮 = U := Subset.antisymm hSubset hSuperset
    simpa [hEq] using hUnion

/-!
Definition 2.5 singles out representative neighborhoods that refine all
neighborhoods of the point.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 2.5: a neighborhood basis at `x`. -/
structure IsNeighborhoodBasis_2_5 {X : Type u}
    (𝒪 : Set (Set X)) (x : X) (𝒰 : Set (Set X)) : Prop where
  isNeighborhood : ∀ U ∈ 𝒰, IsNeighborhood_2_1 𝒪 x U
  hasRefinement : ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V → ∃ U ∈ 𝒰, U ⊆ V

/-!
Example 2.6 says that all neighborhoods of a point form a neighborhood basis.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.6: the family of all neighborhoods of `x` is a neighborhood basis. -/
theorem allNeighborhoods_isNeighborhoodBasis_2_6 {X : Type u} {𝒪 : Set (Set X)} (x : X) :
    IsNeighborhoodBasis_2_5 𝒪 x {V : Set X | IsNeighborhood_2_1 𝒪 x V}
      := {
        isNeighborhood  := λ _ hU   ↦ mem_setOf.mp hU,
        hasRefinement   := λ V hyp  ↦ ⟨V, ⟨
          mem_setOf.mpr hyp,
          LE.le.subset λ ⦃_⦄ a ↦ a
        ⟩⟩
      }

/-!
Example 2.7 says that all open neighborhoods of a point also form a
neighborhood basis.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.7: the family of all open neighborhoods of `x` is a neighborhood basis. -/
theorem allOpenNeighborhoods_isNeighborhoodBasis_2_7 {X : Type u} {𝒪 : Set (Set X)}
    (_𝒪 : IsTopology_1_1 X 𝒪) (x : X) :
    IsNeighborhoodBasis_2_5 𝒪 x {V : Set X | IsOpenNeighborhood_2_1 𝒪 x V} := by
  refine ⟨?_, ?_⟩
  · intro V hV
    exact (mem_setOf.mp hV).1
  · intro V hyp
    rcases hyp with ⟨U, Uop, xinU, UsubV⟩
    refine ⟨U, ?_, UsubV⟩
    simp only [mem_setOf_eq]
    exact ⟨⟨U, Uop, xinU, LE.le.subset λ ⦃_⦄ a ↦ a⟩, Uop⟩

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
  refine ⟨?_, ?_⟩
  · intro U hU
    rcases hU with ⟨r, rpos, rfl⟩
    refine ⟨openBall_1_14 x r, ?_, ?_, LE.le.subset fun ⦃_⦄ a ↦ a⟩
    · exact openBall_open_1_16 x r
    · have hxx : DistanceSpace_1_12.dist x x = 0 :=
        (DistanceSpace_1_12.D1 x x).2 rfl
      simp [openBall_1_14, hxx, rpos]
  · intro V hyp
    rcases hyp with ⟨U, Uop, xinU, UsubV⟩
    specialize Uop x xinU
    rcases Uop with ⟨r, rpos, BinU⟩
    refine ⟨openBall_1_14 x r, ?_, ?_⟩
    · exact ⟨r, rpos, rfl⟩
    · exact LE.le.subset λ ⦃_⦄ a ↦ UsubV (BinU a)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.8: the balls of radius `1 / n` form a countable neighborhood basis. -/
theorem distance_invPNatBall_isNeighborhoodBasis_2_8 {X : Type u}
    [DistanceSpace_1_12 X]
    (x : X) :
    IsNeighborhoodBasis_2_5
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) x
      {U : Set X | ∃ n : ℕ+, U = openBall_1_14 x (1 / (n : ℝ))} := by
  refine ⟨?_, ?_⟩
  · intro U hU
    rcases hU with ⟨n, rfl⟩
    refine (distance_openBall_isNeighborhoodBasis_2_8 x).isNeighborhood _ ?_
    exact ⟨1 / (n : ℝ), by positivity, rfl⟩
  · intro V hyp
    obtain ⟨W, hW, WsubV⟩ := (distance_openBall_isNeighborhoodBasis_2_8 x).hasRefinement V hyp
    rcases hW with ⟨r, rpos, hW⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
    set n' : ℕ+ := ⟨max 1 n, by simp⟩ with n'df
    have hn' : 1 / ↑↑n' < r := by
      rw [n'df]
      field_simp
      have : 1 / r < max 1 ↑n := by
        simp only [one_div, lt_sup_iff]
        grind only
      simp only [PNat.mk_coe, Nat.cast_max, Nat.cast_one, gt_iff_lt]
      exact (mul_inv_lt_iff₀ rpos).mp this
    refine ⟨openBall_1_14 x (1 / (n' : ℝ)), ?_, ?_⟩
    · simp only [one_div, mem_setOf_eq]
      exact ⟨n', rfl⟩
    · have : openBall_1_14 x (1 / (n' : ℝ)) ⊆ W := by
        rw [hW]
        simp only [openBall_1_14, setOf_subset_setOf]
        intro y hy
        exact Std.lt_trans hy hn'
      exact LE.le.subset λ ⦃_⦄ a ↦ WsubV (this a)

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
  refine ⟨?_, ?_⟩
  · intro U hU
    simp only [mem_singleton_iff] at hU
    rw [hU]
    refine ⟨{x}, ?_, by simp only [mem_singleton_iff], LE.le.subset λ ⦃_⦄ a ↦ a⟩
    simp [discreteTopology_1_6]
  · intro V hyp
    refine ⟨{x}, ?_, ?_⟩
    · simp
    · simp only [singleton_subset_iff]
      rcases hyp with ⟨_, _, h1, h2⟩
      exact mem_of_subset_of_mem h2 h1

/-!
Proposition 2.10 packages the characteristic properties `NB1` through `NB4`
  of a neighborhood basis at a fixed point.
A stronger global-family form is kept afterwards for later use in Proposition 2.11.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.10: a globally chosen neighborhood basis at each point. -/
structure IsNeighborhoodBasisFamily_2_10 (X : Type u) (𝒰 : X → Set (Set X)) : Prop where
  NB1_nonempty : ∀ x : X, (𝒰 x).Nonempty
  NB2_mem : ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ 𝒰 x -> x ∈ U
  NB3_inter : ∀ ⦃x : X⦄ ⦃U₁ U₂ : Set X⦄, U₁ ∈ 𝒰 x -> U₂ ∈ 𝒰 x
    -> ∃ V : Set X, V ∈ 𝒰 x ∧ V ⊆ U₁ ∩ U₂

  /-
    There is a little flaw in the original narrative:
      𝒰y was depicted as a neighborhood basis of y,
        which needs a topology structure on X (refer to definition 2_5).
      But in 2_11, we attempt to induce a topology structure
        by using a `X -> Set (Set X)` satisfies NB1 through NB4,
          which means any topology structure on X
            cannot be predefined.
      Thus we use a `𝒰 : X -> Set (Set X)` as an alternative neighborhood basis family
        while leaving the topology definition open.
   -/
  NB4_local : ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ 𝒰 x →
    ∃ V : Set X, V ∈ 𝒰 x ∧ ∀ y ∈ V, ∃ W : Set X, W ∈ 𝒰 y ∧ W ⊆ U

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.10: pointwise chosen neighborhood bases satisfy the stronger
global-family version of `NB1`--`NB4`. -/
theorem neighborhoodBasis_properties_2_10 {X : Type u} {𝒪 : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) {𝒰 : X → Set (Set X)}
    (h𝒰 : ∀ x : X, IsNeighborhoodBasis_2_5 𝒪 x (𝒰 x)) :
    IsNeighborhoodBasisFamily_2_10 X 𝒰 := by
  refine ⟨?_, ?_, ?_, ?_⟩

  /- NB1 and NB2 follows immediately from the definition. -/
  · intro x
    have x_in_univ : x ∈ univ := mem_univ x
    have univ_is_neighbor_of_x : IsNeighborhood_2_1 𝒪 x univ := ⟨
      univ,
      h𝒪.O1_univ,
      x_in_univ,
      univ_subset_iff.mpr rfl
    ⟩
    rcases (h𝒰 x).hasRefinement univ univ_is_neighbor_of_x with ⟨V, hV, _⟩
    exact ⟨V, hV⟩
  · intro x U hU
    rcases (h𝒰 x).isNeighborhood U hU with ⟨V, hV, hxV, VsubU⟩
    exact mem_of_subset_of_mem VsubU hxV

  /- NB3 follows the proposition 2.3. -/
  · intro x U₁ U₂ hU₁ hU₂
    specialize h𝒰 x
    have hU₁ := h𝒰.isNeighborhood _ hU₁
    have hU₂ := h𝒰.isNeighborhood _ hU₂
    have := neighborhood_inter_2_3 h𝒪 x _ hU₁ _ hU₂
    exact h𝒰.hasRefinement (U₁ ∩ U₂) this

  /-
    Finally we try to prove NB4.
    Assume x ∈ X, U ∈ 𝒰 x, since U is a neighborhood,
      There exists U₀ ∈ 𝒪 such that x ∈ U₀ ⊆ U.
    On the other hand,
      U₀ is an open neighborhood of x (proposition 2.2),
        hence there exists V ∈ 𝒰 x satisfy V ⊆ U₀
    Now verify such V is one we attempt to find.
    For all y ∈ V, we have y ∈ U₀.
    Since U₀ ∈ 𝒪, U₀ is a neighborhood of y.
    Thus ∀ y ∈ V, ∃ W ∈ 𝒰 y, W ⊆ U₀ ⊆ U.
  -/
  · intro x U hU
    obtain ⟨U₀, U₀op, xinU₀, U₀subU⟩ := (h𝒰 x).isNeighborhood U hU
    have U₀_is_open_neighborhood_of_x
      := (openNeighborhood_iff_2_2 h𝒪 x U₀).mpr ⟨U₀op, xinU₀⟩
    obtain ⟨V, hV, VsubU₀⟩
      := (h𝒰 x).hasRefinement _ U₀_is_open_neighborhood_of_x.left
    use V; use hV; intro y hy;
    have yinU₀ : y ∈ U₀ := mem_of_subset_of_mem VsubU₀ hy
    have U₀_is_neighborhood_of_y : IsNeighborhood_2_1 𝒪 y U₀ := by
      use U₀
    obtain ⟨W, hW, WsubU₀⟩
      := (h𝒰 y).hasRefinement U₀ U₀_is_neighborhood_of_y
    have WsubU : W ⊆ U := LE.le.subset λ ⦃_⦄ a ↦ U₀subU (WsubU₀ a)
    exact ⟨W, hW, WsubU⟩

/-!
Proposition 2.11 reconstructs a topology from pointwise neighborhood-basis families,
  which satisfying `NB1` through `NB4`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.11: the open family generated by prescribed neighborhood bases. -/
def topologyFromNeighborhoodBases_2_11 {X : Type u} (𝒰 : X → Set (Set X)) : Set (Set X) :=
  {U : Set X | ∀ x ∈ U, ∃ V ∈ 𝒰 x, V ⊆ U}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 2.11: neighborhood-basis axioms determine a unique topology. -/
structure NeighborhoodBasisTopologyData_2_11 {X : Type u}
    (𝒰 : X → Set (Set X)) : Prop where
  isTopology  :
    IsTopology_1_1 X (topologyFromNeighborhoodBases_2_11 𝒰)
  isBasis     :
    ∀ x : X, IsNeighborhoodBasis_2_5 (topologyFromNeighborhoodBases_2_11 𝒰) x (𝒰 x)
  unique      :
    ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 ->
      (∀ x : X, IsNeighborhoodBasis_2_5 𝒪 x (𝒰 x)) ->
        𝒪 = topologyFromNeighborhoodBases_2_11 𝒰

theorem topology_from_neighborhoodBases_2_11 {X : Type u} [Nonempty X] {𝒰 : X → Set (Set X)}
    (h𝒰 : IsNeighborhoodBasisFamily_2_10 X 𝒰) :
    NeighborhoodBasisTopologyData_2_11 𝒰 := {
      isTopology  := {
        O1_empty    := λ x x_in_empty ↦ not_disjoint_iff.mp λ _ ↦ x_in_empty,
        O1_univ     := by
          intro x x_in_univ
          have ⟨V, hV⟩ := h𝒰.NB1_nonempty x
          use V; use hV;
          exact subset_univ _,
        O2_inter    := by
          intro U₁ U₂ hU₁ hU₂ x hx
          specialize hU₁ x hx.left
          specialize hU₂ x hx.right
          rcases hU₁ with ⟨U₁', hU₁'⟩
          rcases hU₂ with ⟨U₂', hU₂'⟩
          have ⟨V, hV, Vsub⟩ := h𝒰.NB3_inter hU₁'.left hU₂'.left
          use V; use hV;
          grind only [= subset_def, = mem_inter_iff],
        O3_sUnion   := by
          intro 𝒮 hyp x xinU𝒮
          have ⟨U₀, hU₀, xinU₀⟩ : ∃ U₀ ∈ 𝒮, x ∈ U₀ := mem_sUnion.mp xinU𝒮
          specialize hyp U₀ hU₀ x xinU₀
          rcases hyp with ⟨V, hV, VsubU₀⟩
          use V; use hV;
          exact subset_sUnion_of_subset 𝒮 U₀ VsubU₀ hU₀,
      },
      isBasis     := by
        set 𝒪 := topologyFromNeighborhoodBases_2_11 𝒰
          with 𝒪df
        intro x
        set 𝒰x  : Set (Set X) := 𝒰 x with Udf
        set U'  : (U : Set X) -> U ∈ 𝒰x -> Set X
          := λ U _ ↦ {y : X | y ∈ U ∧ ∃ V ∈ 𝒰 y, V ⊆ U}
            with U'df
        have U'subU : (U : Set X) -> (hU : U ∈ 𝒰x) -> U' U hU ⊆ U := by
          intro U hU x hx
          simp [U'df] at hx
          exact hx.left
        have c1 : ∀ U : Set X, (hU : U ∈ 𝒰x) -> x ∈ U' U hU := by
          simp only [U'df, mem_setOf_eq]
          intro U hU
          rw [Udf] at hU
          constructor
          · exact h𝒰.NB2_mem hU
          · use U
        have c2 : ∀ U : Set X, (hU : U ∈ 𝒰x) -> U' U hU ∈ 𝒪 := by
          intro U hU y hy
          rcases hy with ⟨yinU, V, hV, VsubU⟩
          have := h𝒰.NB4_local hV
          rcases this with ⟨V', hV', hz⟩
          change ∀ z ∈ V', ∃ W ∈ 𝒰 z, W ⊆ V at hz
          have zinW : ∀ z ∈ V', ∃ W ∈ 𝒰 z, z ∈ W ∧ W ⊆ V:= by
            intro z zinV'
            specialize hz z zinV'
            rcases hz with ⟨W, hW, WsubV⟩
            use W; exact ⟨
              hW, h𝒰.NB2_mem hW,
              WsubV,
            ⟩
          have V'subV : V' ⊆ V := by
            intro z hz
            specialize zinW z hz
            rcases zinW with ⟨W, _, hW, WsubV⟩
            exact mem_of_subset_of_mem WsubV hW
          have V'subU' : V' ⊆ U' U hU := by
            intro z zinV'
            constructor
            · exact mem_of_subset_of_mem
                VsubU (V'subV zinV')
            · specialize hz z zinV'
              rcases hz with ⟨W, hW, WsubV⟩
              use W
              exact And.symm ⟨
                λ ⦃_⦄ a ↦ VsubU (WsubV a), hW
              ⟩
          use V'
        have c3 : ∀ U ∈ 𝒰x, IsNeighborhood_2_1 𝒪 x U := by
          intro U hU
          specialize U'subU U hU
          specialize c1 U hU
          specialize c2 U hU
          use U' U hU

        constructor
        · intro U hU
          exact c3 U hU
        · intro V hV
          unfold IsNeighborhood_2_1 at hV
          rcases hV with ⟨U₀, hU₀, xinU₀, U₀subV⟩
          specialize hU₀ x xinU₀
          rcases hU₀ with ⟨U, hU, UsubU₀⟩
          have UsubV : U ⊆ V
            := LE.le.subset λ ⦃_⦄ a ↦ U₀subV (UsubU₀ a)
          use U;,
      unique      := by
        intro 𝒪 h𝒪 hyp
        ext U
        constructor
        · intro hU x xinU
          specialize hyp x
          have U_is_neighborhood_of_x :=
            (openNeighborhood_iff_2_2 h𝒪 x U).mpr ⟨hU, xinU⟩
          exact hyp.hasRefinement U U_is_neighborhood_of_x.left
        · intro hU
          apply (isOpen_iff_neighborhood_2_4 h𝒪 U).mpr
          intro x xinU
          specialize hU x xinU
          specialize hyp x
          rcases hU with ⟨V, hV, VsubU⟩
          rcases hyp with ⟨hyp, _⟩
          specialize hyp V hV
          use V;
    ,
    }

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
    FirstCountable_2_12 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) :=
    open Classical in by
      intro x
      set 𝒰 := {U | ∃ n : ℕ+, U = openBall_1_14 x (1 / ↑↑n)} with 𝒰df
      have h𝒰 := distance_invPNatBall_isNeighborhoodBasis_2_8 x
      rw [← 𝒰df] at h𝒰
      use 𝒰; use h𝒰;
      refine Set.countable_iff_exists_injective.mpr ?_
      have : ∀ U : 𝒰.Elem, ∃ n : ℕ, U.val = openBall_1_14 x (1 / ↑n) := by
        rintro ⟨U, Uin𝒰⟩
        rcases Uin𝒰 with ⟨⟨n, npos⟩, hn⟩
        simp only [PNat.mk_coe, one_div] at hn ⊢
        use n

      /- Here we need a injective function which seems hardly avoid choosing. -/
      choose f hf using this
      use f
      intro U₁' U₂' hU'
      have hU₁ := hf U₁'
      have hU₂ := hf U₂'
      apply Subtype.ext
      rw [hU₁, hU₂]
      rw [hU']

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.13: every discrete space is first countable. -/
theorem discreteSpace_firstCountable_2_13 {X : Type u} :
    FirstCountable_2_12 (discreteTopology_1_6 X)
  := λ x ↦ ⟨{{x}}, ⟨
    discrete_singleton_isNeighborhoodBasis_2_9 x,
    countable_singleton ({x} : Set X),
  ⟩⟩

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.13: every metrizable space is first countable. -/
theorem metrizableSpace_firstCountable_2_13 {X : Type u} {𝒪 : Set (Set X)}
    (hM : IsMetrizable_1_18 𝒪) :
    FirstCountable_2_12 𝒪 := by
  rcases hM with ⟨D, hyp⟩
  rw [← hyp]
  exact @distanceSpace_firstCountable_2_13 X D

/-!
Example 2.14 discusses first countability for the cofinite topology.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.14: a countable cofinite space is first countable. -/
theorem countable_finiteComplement_firstCountable_2_14 {X : Type u}
    (hX : Set.Countable (univ : Set X)) :
    FirstCountable_2_12 (finiteComplementTopology_1_8 X) := by
  intro x
  set 𝒰 := {U : Set X | ∃ O, Set.Finite Oᶜ ∧ U = O ∪ {x}} with 𝒰df
  set 𝒪 := finiteComplementTopology_1_8 X with 𝒪df
  have : IsNeighborhoodBasis_2_5 𝒪 x 𝒰 := by
    refine ⟨?_, ?_⟩
    · intro U hU
      simp only [𝒰df, mem_setOf_eq] at hU
      rcases hU with ⟨O, O_compl_fin, Ueq⟩
      use U
      constructor
      · right
        rw [Ueq, compl_union];
        exact Finite.inter_of_left O_compl_fin {x}ᶜ
      · constructor
        · simp [Ueq]
        · exact LE.le.subset λ ⦃_⦄ ↦ id
    · intro V hV
      rcases hV with ⟨O, Oop, xinO, OsubV⟩
      rcases Oop with O_empty | F_fin
      · rw [O_empty] at xinO
        exact not_disjoint_iff.mp λ a ↦ xinO
      · have : O ∈ 𝒰 := by
          simp only [𝒰df, mem_setOf_eq]
          use O
          constructor
          · exact F_fin
          · ext x'
            constructor
            · exact λ a ↦ mem_union_left {x} a
            · intro hx'
              rcases hx' with hx' | hx'
              · exact hx'
              · rw [hx']
                exact xinO
        use O
  use 𝒰; use this;
  haveI : Countable X := Set.countable_univ_iff.mp hX
  have hfiniteCompl : ∀ U ∈ 𝒰, Set.Finite Uᶜ := by
    intro U hU
    rcases hU with ⟨O, hO, rfl⟩
    convert Finite.inter_of_left hO {x}ᶜ using 1
    ext y
    simp [and_comm]
  have hFiniteSets : ({F : Set X | F.Finite} : Set (Set X)).Countable :=
    Set.Countable.setOf_finite
  haveI : Countable {F : Set X | F.Finite} := hFiniteSets.to_subtype
  change Countable 𝒰
  let f : 𝒰 → {F : Set X | F.Finite} := fun U => ⟨U.1ᶜ, hfiniteCompl U.1 U.2⟩
  refine Function.Injective.countable (f := f) ?_
  intro U₁ U₂ h
  apply Subtype.ext
  ext y
  have hy : (y ∉ U₁.1ᶜ) = (y ∉ U₂.1ᶜ) := congrArg (fun s => y ∉ s) (congrArg Subtype.val h)
  simpa using hy

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 2.14: an uncountable cofinite space is not first countable. -/
theorem uncountable_finiteComplement_not_firstCountable_2_14 {X : Type u}
    (hX : ¬ Set.Countable (univ : Set X)) :
    ¬ FirstCountable_2_12 (finiteComplementTopology_1_8 X) :=
  open Classical in by
    intro hyp
    have hne : (univ : Set X).Nonempty := by
      by_contra hEmpty
      apply hX
      rw [Set.not_nonempty_iff_eq_empty] at hEmpty
      rw [hEmpty]
      exact (Set.toFinite (∅ : Set X)).countable
    rcases hne with ⟨x, _⟩
    rcases hyp x with ⟨𝒰, hBasis, h𝒰count⟩
    have hOpenWitness : ∀ U ∈ 𝒰, ∃ O : Set X, O ∈ finiteComplementTopology_1_8 X ∧ x ∈ O ∧ O ⊆ U :=
      hBasis.isNeighborhood
    choose O hOop hxO hOsub using hOpenWitness
    have hOcomplFinite : ∀ U (hU : U ∈ 𝒰), Set.Finite (O U hU)ᶜ := by
      intro U hU
      have h := hOop U hU
      rcases h with hEmpty | hfin
      · exfalso
        simpa [hEmpty] using hxO U hU
      · exact hfin
    let S : Set X := ⋃ u : 𝒰, (O u.1 u.2)ᶜ
    have hScount : S.Countable := by
      unfold S
      haveI : Countable 𝒰 := h𝒰count.to_subtype
      exact Set.countable_iUnion fun u ↦ (hOcomplFinite u.1 u.2).countable
    have hSxcount : (insert x S).Countable := hScount.insert x
    obtain ⟨y, hyx, hyS⟩ : ∃ y : X, y ≠ x ∧ y ∉ S := by
      by_contra h
      apply hX
      have hall : ∀ y : X, y ∈ insert x S := by
        intro y
        by_contra hy
        apply h
        exact ⟨y, by simpa [Set.mem_insert_iff] using hy⟩
      exact Set.Countable.mono (fun y _ ↦ hall y) hSxcount
    have hV : IsNeighborhood_2_1 (finiteComplementTopology_1_8 X) x ({y}ᶜ) := by
      refine ⟨{y}ᶜ, ?_, ?_, fun _ ha ↦ ha⟩
      · simp [finiteComplementTopology_1_8]
      · simpa [Set.mem_singleton_iff] using hyx.symm
    rcases hBasis.hasRefinement {y}ᶜ hV with ⟨U, hU𝒰, hUsub⟩
    have hyU : y ∈ U := by
      by_contra hyU
      apply hyS
      unfold S
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨U, hU𝒰⟩, ?_⟩
      intro hyOU
      exact hyU (hOsub U hU𝒰 hyOU)
    have : y ∈ ({y}ᶜ : Set X) := hUsub hyU
    simp only [mem_compl_iff, mem_singleton_iff,
      not_true_eq_false] at this

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

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : Euclidean space carries our distance-space structure. -/
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

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our neighborhood agrees with membership in `𝓝 x`. -/
theorem isNeighborhood_iff_mem_nhds_cert {X : Type u} (T : TopologicalSpace X) (x : X) (V : Set X) :
    IsNeighborhood_2_1 {U : Set X | @IsOpen X T U} x V ↔ V ∈ nhds x := by
  sorry

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our topological sequence convergence matches filter convergence in mathlib. -/
theorem tendstoSeq_iff_tendsto_cert {X : Type u} (T : TopologicalSpace X)
    (xₙ : Sequence_2_16 X) (x : X) :
    TendstoSeq_2_16 {U : Set X | @IsOpen X T U} xₙ x ↔ Filter.Tendsto xₙ Filter.atTop (nhds x) := by
  sorry

end NeighborhoodBasis
end LeanTopology
