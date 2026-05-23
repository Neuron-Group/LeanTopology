import LeanTopology.ClosureInterior
import LeanTopology.Tactic.TopologyIntro
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# 拓扑学入门5: 连续映射
-/

noncomputable section

open Set LeanTopology.EuclideanSpaceTopology

namespace LeanTopology
namespace ContinuousMap

universe u v w

open LeanTopology.TopologicalSpace
open LeanTopology.NeighborhoodBasis
open LeanTopology.Basis
open LeanTopology.ClosureInterior

section TopologyPart

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {𝒪₁ : Set (Set X)} {𝒪₂ : Set (Set Y)} {𝒪₃ : Set (Set Z)}

/-!
Definition 5.1 introduces continuity by preservation of openness under
preimages.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 5.1: a map is continuous when the preimage of every open set is open. -/
def IsContinuous_5_1 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) (f : X → Y) : Prop :=
  ∀ V : Set Y, V ∈ 𝒪₂ -> f ⁻¹' V ∈ 𝒪₁

/-!
Proposition 5.2 records the continuity of identity maps and compositions.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.2 (1): the identity map is continuous. -/
theorem id_continuous_5_2 :
    IsContinuous_5_1 𝒪₁ 𝒪₁ (id : X → X) := by
  intro V Vop
  rw [preimage_id_eq, id_eq]
  assumption

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.2 (2): the composition of continuous maps is continuous. -/
theorem continuous_comp_5_2 {f : X → Y} {g : Y → Z}
  (hf : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
  (hg : IsContinuous_5_1 𝒪₂ 𝒪₃ g) :
    IsContinuous_5_1 𝒪₁ 𝒪₃ (g ∘ f) := by
  intro V Vop
  rw [preimage_comp]
  specialize hg V Vop
  exact hf (g ⁻¹' V) hg

/-- A map is constant when all its values coincide with one fixed point. -/
def IsConstantMap_5_3 (f : X → Y) : Prop :=
  ∃ c : Y, ∀ x : X, f x = c

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.3: every constant map is continuous. -/
theorem constantMap_continuous_5_3 (h𝒪₁ : IsTopology_1_1 X 𝒪₁) {f : X → Y}
  (hf : IsConstantMap_5_3 f) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f := by
  rcases hf with ⟨c, hf⟩
  intro V Vop
  by_cases hyp : c ∈ V
  · have : f ⁻¹' V = univ := by
      ext x
      simp [hf x, hyp]
    rw [this]
    exact h𝒪₁.O1_univ
  · have : f ⁻¹' V = ∅ := by
      ext x
      simp [hf x, hyp]
    rw [this]
    exact h𝒪₁.O1_empty

/-!
Proposition 5.4 rewrites continuity using closed sets.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.4: continuity is equivalent to preservation of closedness under preimages. -/
theorem continuous_iff_preimage_closed_5_4
  (f : X → Y) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f
      <->
        ∀ F : Set Y, IsClosed_1_2 𝒪₂ F -> IsClosed_1_2 𝒪₁ (f ⁻¹' F) := by
  constructor<;>intro hyp
  · intro F Fcl
    set U := Fᶜ
    have Uop : U ∈ 𝒪₂ := open_of_closed_compl Fcl
    have : f ⁻¹' F = (f ⁻¹' U)ᶜ
      := eq_compl_comm.mp rfl
    rw [this]
    specialize hyp U Uop
    exact isClosed_compl_iff_open (f ⁻¹' U)
      |>.mpr hyp
  · intro U Uop
    set F := Uᶜ
    have Fcl : IsClosed_1_2 𝒪₂ F
      := isClosed_compl_iff_open U |>.mpr Uop
    have : f ⁻¹' U = (f ⁻¹' F)ᶜ
      := eq_compl_comm.mp rfl
    rw [this]
    specialize hyp F Fcl
    exact open_of_closed_compl hyp

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.5 (1): every map from a discrete space is continuous. -/
theorem continuous_from_discrete_5_5 (f : X → Y) :
    IsContinuous_5_1 (discreteTopology_1_6 X) 𝒪₂ f := by
  intro _ _
  exact mem_discreteTopology_1_6 _

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.5 (2): every map into an indiscrete space is continuous. -/
theorem continuous_to_indiscrete_5_5 (h𝒪₁ : IsTopology_1_1 X 𝒪₁) (f : X → Y) :
    IsContinuous_5_1 𝒪₁ (indiscreteTopology_1_7 Y) f := by
  intro V Vop
  simp only [indiscreteTopology_1_7, mem_insert_iff, mem_singleton_iff] at Vop
  rcases Vop with rfl | rfl
  · simpa using h𝒪₁.O1_empty
  · simpa using h𝒪₁.O1_univ

/-!
Definition 5.6 introduces continuity at a point.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 5.6: `f` is continuous at `x` when neighborhoods of `f x`
pull back to neighborhoods of `x`. -/
def IsContinuousAt_5_6 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y))
    (f : X → Y) (x : X) : Prop :=
  ∀ V : Set Y, IsNeighborhood_2_1 𝒪₂ (f x) V ->
    ∃ U : Set X, IsNeighborhood_2_1 𝒪₁ x U ∧ U ⊆ f ⁻¹' V

/-!
Propositions 5.7 and 5.8 compare global continuity and pointwise continuity.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.7: a map is continuous iff it is continuous at every point. -/
theorem continuous_iff_continuousAt_5_7
  (h𝒪₁ : IsTopology_1_1 X 𝒪₁) (f : X → Y) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f <-> ∀ x : X, IsContinuousAt_5_6 𝒪₁ 𝒪₂ f x := by
  constructor<;>intro hyp
  · intro x V hV
    rcases hV with ⟨V', V'op, hV', V'subV⟩
    specialize hyp V' V'op
    have sub : f ⁻¹' V' ⊆ f ⁻¹' V := preimage_mono V'subV
    have mem : x ∈ f ⁻¹' V' := mem_preimage.mpr hV'
    use f ⁻¹' V'; constructor
    · use f ⁻¹' V'
    · assumption
  · intro V Vop₂
    apply isOpen_iff_neighborhood_2_4 h𝒪₁ (f ⁻¹' V) |>.mpr
    intro x hx
    have fx_mem : f x ∈ V := mem_preimage.mp hx
    have hV : IsNeighborhood_2_1 𝒪₂ (f x) V := by use V
    exact hyp x V hV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.8: continuity at a point may be tested on neighborhood bases. -/
theorem continuousAt_iff_neighborhoodBasis_5_8
    {f : X → Y} {x : X} {𝒰 : Set (Set X)} {𝒱 : Set (Set Y)}
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪₁ x 𝒰)
    (h𝒱 : IsNeighborhoodBasis_2_5 𝒪₂ (f x) 𝒱) :
    IsContinuousAt_5_6 𝒪₁ 𝒪₂ f x
      <-> ∀ V : Set Y, V ∈ 𝒱 -> ∃ U : Set X, U ∈ 𝒰 ∧ U ⊆ f ⁻¹' V := by
  constructor<;>intro hyp
  · intro V hV
    rcases h𝒱 with ⟨h𝒱, -⟩
    specialize h𝒱 V hV
    specialize hyp V h𝒱
    rcases hyp with ⟨U₀, hU₀, U₀sub⟩
    rcases h𝒰 with ⟨-, hrefine⟩
    rcases hrefine U₀ hU₀ with ⟨U, hU, hUU₀⟩
    refine ⟨U, hU, ?_⟩
    exact hUU₀.trans U₀sub
  · intro V hV
    rcases h𝒱 with ⟨-, h𝒱⟩
    rcases h𝒰 with ⟨h𝒰, -⟩
    specialize h𝒱 V hV
    rcases h𝒱 with ⟨V', hV', V'subV⟩
    specialize hyp V' hV'
    rcases hyp with ⟨U, hU, Usub⟩
    specialize h𝒰 U hU
    have : U ⊆ f ⁻¹' V := by
      have : f ⁻¹' V' ⊆ f ⁻¹' V
        := preimage_mono V'subV
      exact MapsTo.subset_preimage
        λ ⦃_⦄ a ↦ V'subV (Usub a)
    use U

end TopologyPart

section MetricPart

variable {X : Type u} {Y : Type v}
variable [DistanceSpace_1_12 X] [DistanceSpace_1_12 Y]

open LeanTopology.TopologicalSpace
open LeanTopology.TopologicalSpace.DistanceSpace_1_12

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.9(a): topological continuity is equivalent to the open-ball image formulation. -/
theorem continuous_iff_ball_5_9 (f : X → Y) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›) f
        <->
          ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
            f '' openBall_1_14 x₀ δ ⊆ openBall_1_14 (f x₀) ε := by
  topo_auto 𝒪₁ h𝒪₁ for X := @inducedTopology_1_17 X ‹DistanceSpace_1_12 X›
  topo_auto 𝒪₂ h𝒪₂ for Y := @inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›
  constructor<;>intro hyp
  · intro x₀ ε εpos
    have h𝒰 := x₀   |> distance_openBall_isNeighborhoodBasis_2_8
    set 𝒰 := {U | ∃ r > 0, U = openBall_1_14 x₀ r}
    have h𝒱 := f x₀ |> distance_openBall_isNeighborhoodBasis_2_8
    set 𝒱 := {V | ∃ r > 0, V = openBall_1_14 (f x₀) r}
    change IsNeighborhoodBasis_2_5 𝒪₁ x₀ 𝒰 at h𝒰
    change IsNeighborhoodBasis_2_5 𝒪₂ (f x₀) 𝒱 at h𝒱
    have hyp := continuousAt_iff_neighborhoodBasis_5_8 h𝒰 h𝒱
      |>.mp (continuous_iff_continuousAt_5_7 h𝒪₁ f
        |>.mp hyp x₀)
    have : openBall_1_14 (f x₀) ε ∈ 𝒱 := by
      simp only [gt_iff_lt, mem_setOf_eq, 𝒱]; use ε
    specialize hyp (openBall_1_14 (f x₀) ε) this
    rcases hyp with ⟨U, hU, Usub⟩
    simp only [gt_iff_lt, mem_setOf_eq, 𝒰] at hU
    rcases hU with ⟨δ, δpos, Ueq⟩
    use δ; use δpos
    rw [Ueq] at Usub
    exact image_subset_iff.mpr Usub
  · apply continuous_iff_continuousAt_5_7 h𝒪₁ f |>.mpr
    intro x₀
    have h𝒰 := x₀   |> distance_openBall_isNeighborhoodBasis_2_8
    set 𝒰 := {U | ∃ r > 0, U = openBall_1_14 x₀ r}
    have h𝒱 := f x₀ |> distance_openBall_isNeighborhoodBasis_2_8
    set 𝒱 := {V | ∃ r > 0, V = openBall_1_14 (f x₀) r}
    change IsNeighborhoodBasis_2_5 𝒪₁ x₀ 𝒰 at h𝒰
    change IsNeighborhoodBasis_2_5 𝒪₂ (f x₀) 𝒱 at h𝒱
    apply continuousAt_iff_neighborhoodBasis_5_8 h𝒰 h𝒱 |>.mpr
    intro V hV
    simp only [gt_iff_lt, mem_setOf_eq, 𝒱] at hV
    rcases hV with ⟨ε, εpos, Veq⟩
    specialize hyp x₀ ε εpos
    rcases hyp with ⟨δ, δpos, sub⟩
    use openBall_1_14 x₀ δ
    constructor
    · simp only [gt_iff_lt, mem_setOf_eq, 𝒰]; use δ
    · rw [Veq]
      exact image_subset_iff.mp sub

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.9(b): the open-ball image formulation is equivalent to the usual epsilon-delta condition. -/
theorem ballImage_iff_eps_5_9 (f : X → Y) :
  (∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
    f '' openBall_1_14 x₀ δ ⊆ openBall_1_14 (f x₀) ε)
      <->
        ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
          ∀ x : X, dist x₀ x < δ -> dist (f x₀) (f x) < ε := by
  constructor
  · intro h x₀ ε εpos
    rcases h x₀ ε εpos with ⟨δ, δpos, hsub⟩
    use δ
    constructor
    · exact δpos
    · intro x hx
      have hfx : f x ∈ f '' openBall_1_14 x₀ δ := by
        use x
        simp [openBall_1_14, hx]
      exact hsub hfx
  · intro h x₀ ε εpos
    rcases h x₀ ε εpos with ⟨δ, δpos, hδ⟩
    use δ
    constructor
    · exact δpos
    · intro y hy
      rcases hy with ⟨x, hxball, rfl⟩
      exact hδ x hxball

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.9: metric continuity is equivalent to the usual epsilon-delta formulation. -/
theorem continuous_iff_eps_5_9 (f : X → Y) :
  IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›) f
      <->
        ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
          ∀ x : X, dist x₀ x < δ -> dist (f x₀) (f x) < ε := by
  exact (continuous_iff_ball_5_9 f).trans (ballImage_iff_eps_5_9 f)

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.10: a map into Euclidean space is continuous iff each coordinate is continuous. -/
theorem continuous_into_euclidean_5_10 {n : ℕ} (f : X → E n) :
  IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n)) f
      <->
        ∀ i : Fin n,
          IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
            (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ f x i) := by
  topo_auto 𝒪₁ h𝒪₁ for X := @inducedTopology_1_17 X ‹DistanceSpace_1_12 X›
  topo_auto 𝒪₂ h𝒪₂ for (E n) := @inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n)
  topo_auto 𝒪' h𝒪' for ℝ := @inducedTopology_1_17 ℝ inferInstance
  set f' := λ i ↦ λ x ↦ (f x).ofLp i
  constructor<;>intro hyp
  · intro i
    change f' i |> IsContinuous_5_1 𝒪₁ 𝒪'
    apply continuous_iff_eps_5_9 (f' i) |>.mpr
    have hyp := continuous_iff_eps_5_9 f |>.mp hyp
    intro x₀ ε εpos
    specialize hyp x₀ ε εpos
    rcases hyp with ⟨δ, δpos, hyp⟩
    use δ; use δpos; intro x hx
    specialize hyp x hx
    have dist_eq : DistanceSpace_1_12.dist (f x₀) (f x)
      = √(∑ i : Fin n,
        (DistanceSpace_1_12.dist (f' i x₀) (f' i x)) ^ 2) := by
      simpa [f'] using dist_eq_sqrt_sum_coordDist_sq_0_3 (f x₀) (f x)
    have : DistanceSpace_1_12.dist (f' i x₀) (f' i x)
      ≤ DistanceSpace_1_12.dist (f x₀) (f x) := by
      rw [dist_eq]
      refine (sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp ?_
      calc
        DistanceSpace_1_12.dist (f' i x₀) (f' i x) ^ 2
            ≤ ∑ j : Fin n,
              (DistanceSpace_1_12.dist (f' j x₀) (f' j x)) ^ 2 := by
                simpa using
                  (Finset.single_le_sum
                    (f := λ j : Fin n ↦
                      (DistanceSpace_1_12.dist (f' j x₀) (f' j x)) ^ 2)
                    (fun _ _ ↦ sq_nonneg _)
                    (by simp))
        _ = (√(∑ j : Fin n,
              (DistanceSpace_1_12.dist (f' j x₀) (f' j x)) ^ 2)) ^ 2 := by
              rw [Real.sq_sqrt]
              exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    exact lt_of_le_of_lt this hyp
  · apply continuous_iff_eps_5_9 f |>.mpr
    have hyp := λ i : Fin n
      ↦ continuous_iff_eps_5_9 (f' i) |>.mp (hyp i)
    intro x₀ ε εpos
    by_cases hn : n = 0
    · subst hn
      refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      have hfx : f x = f x₀ := by
        ext i
        exact Fin.elim0 i
      rw [(DistanceSpace_1_12.D1 _ _).mpr hfx.symm]
      exact εpos
    · have hnpos : 0 < n := Nat.pos_iff_ne_zero.mpr hn
      let i0 : Fin n := ⟨0, hnpos⟩
      have hsqrtpos : 0 < ε / √n := by
        exact div_pos εpos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hnpos))
      have hyp := λ i : Fin n ↦ hyp i x₀ (ε / √n) hsqrtpos
      fin_choose hypf h_hypf using hyp
      have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i0, by simp⟩
      set δ := Finset.univ.inf' huniv hypf
      have δpos : 0 < δ := by
        rw [show δ = Finset.univ.inf' huniv hypf by rfl]
        exact (Finset.lt_inf'_iff (s := Finset.univ) (H := huniv) (f := hypf) (a := 0)).2
          (fun i hi ↦ (h_hypf i).left)
      use δ; use δpos; intro x hx
      have hδ : ∀ i : Fin n, dist x₀ x < hypf i := by
        intro i
        exact lt_of_lt_of_le hx (Finset.inf'_le _ (Finset.mem_univ i))
      have h_hypf := λ i : Fin n ↦ h_hypf i |>.right x (hδ i)
      have dist_eq : DistanceSpace_1_12.dist (f x₀) (f x)
        = √(∑ i : Fin n,
          (DistanceSpace_1_12.dist (f' i x₀) (f' i x)) ^ 2) := by
        simpa [f'] using dist_eq_sqrt_sum_coordDist_sq_0_3 (f x₀) (f x)
      rw [dist_eq]
      have hsq_le :
          ∀ k ∈ (Finset.univ : Finset (Fin n)),
            (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2 ≤ (ε / √n) ^ 2 := by
        intro k hk
        have hk' := h_hypf k
        have hnonneg1 : 0 ≤ DistanceSpace_1_12.dist (f' k x₀) (f' k x) := dist_nonneg
        have hnonneg2 : 0 ≤ ε / √n := by positivity
        nlinarith
      have hsq_lt :
          ∃ k ∈ (Finset.univ : Finset (Fin n)),
            (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2 < (ε / √n) ^ 2 := by
        refine ⟨⟨0, hnpos⟩, by simp, ?_⟩
        have h0 := h_hypf ⟨0, hnpos⟩
        have hnonneg1 :
          0 ≤ DistanceSpace_1_12.dist (f' ⟨0, hnpos⟩ x₀) (f' ⟨0, hnpos⟩ x)
            := dist_nonneg
        have hnonneg2 : 0 ≤ ε / √n := by positivity
        nlinarith
      have hsum_lt :
          ∑ k : Fin n, (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2 <
            ∑ k : Fin n, (ε / √n) ^ 2 := by
        simpa using
          (Finset.sum_lt_sum
            (s := Finset.univ)
            hsq_le
            hsq_lt)
      have hnormsq :
          (√(∑ k : Fin n,
            (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2)) ^ 2 < ε ^ 2 := by
        calc
          (√(∑ k : Fin n,
            (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2)) ^ 2
              = ∑ k : Fin n,
                  (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2 := by
                    rw [Real.sq_sqrt]
                    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
          _ < ∑ k : Fin n, (ε / √n) ^ 2 := hsum_lt
          _ = (n : ℝ) * (ε / √n) ^ 2 := by simp
          _ = ε ^ 2 := by
            field_simp [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hnpos)).ne']
            rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have hsqrt_nonneg : 0 ≤ √(∑ k : Fin n,
          (DistanceSpace_1_12.dist (f' k x₀) (f' k x)) ^ 2) := Real.sqrt_nonneg _
      nlinarith

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.10, subspace form: a map into a Euclidean subspace is continuous iff each coordinate is continuous. -/
theorem continuous_into_euclideanSubspace_5_10 {n : ℕ}
  {A : Set (E n)} (f : X → A) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (euclideanSubspaceTopology_2_21 n A) f
        <->
          ∀ i : Fin n,
            IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
              (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ (f x).1 i) := by
  letI : DistanceSpace_1_12 A := restrictDistance_1_13 (D := euclideanDistanceSpace_1_12 n) A
  have hsub :
      IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
        (euclideanSubspaceTopology_2_21 n A) f
          <->
            IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
              (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n)) (λ x : X ↦ (f x).1) := by
    rw [continuous_iff_eps_5_9, continuous_iff_eps_5_9]
    constructor
    · intro hf x₀ ε εpos
      rcases hf x₀ ε εpos with ⟨δ, δpos, hδ⟩
      refine ⟨δ, δpos, ?_⟩
      intro x hx
      simpa [restrictDistance_1_13] using hδ x hx
    · intro hf x₀ ε εpos
      rcases hf x₀ ε εpos with ⟨δ, δpos, hδ⟩
      refine ⟨δ, δpos, ?_⟩
      intro x hx
      simpa [restrictDistance_1_13] using hδ x hx
  exact hsub.trans (continuous_into_euclidean_5_10 (λ x : X ↦ (f x).1))

/-- ℕℴ𝓉ℯ 5.11: each coordinate projection on a Euclidean subspace is continuous. -/
theorem projection_continuous_5_11 {n : ℕ} (A : Set (E n)) (i : Fin n) :
    IsContinuous_5_1 (euclideanSubspaceTopology_2_21 n A)
      (@inducedTopology_1_17 ℝ inferInstance) (λ x : A ↦ x.1 i) := by
  letI : DistanceSpace_1_12 A := restrictDistance_1_13 (D := euclideanDistanceSpace_1_12 n) A
  have hid : IsContinuous_5_1 (euclideanSubspaceTopology_2_21 n A)
      (euclideanSubspaceTopology_2_21 n A) (id : A → A) := by
    simpa using (id_continuous_5_2 (X := A) (𝒪₁ := euclideanSubspaceTopology_2_21 n A))
  exact (continuous_into_euclideanSubspace_5_10 (X := A) (A := A) (f := id)).mp hid i

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: the sum of two continuous real-valued maps is continuous. -/
theorem continuous_add_real_5_12 (f g : X → ℝ)
  (hf : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) f)
  (hg : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) g) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ f x + g x) := by
  rw [continuous_iff_eps_5_9] at hf hg ⊢
  intro x₀ ε εpos
  have hε2 : 0 < ε / 2 := by linarith
  rcases hf x₀ (ε / 2) hε2 with ⟨δf, δfpos, hδf⟩
  rcases hg x₀ (ε / 2) hε2 with ⟨δg, δgpos, hδg⟩
  refine ⟨min δf δg, by positivity, ?_⟩
  intro x hx
  have hfx : |f x₀ - f x| < ε / 2 := by
    simpa [Real.dist_eq] using hδf x (lt_of_lt_of_le hx (min_le_left _ _))
  have hgx : |g x₀ - g x| < ε / 2 := by
    simpa [Real.dist_eq] using hδg x (lt_of_lt_of_le hx (min_le_right _ _))
  change |(f x₀ + g x₀) - (f x + g x)| < ε
  have hadd : |(f x₀ - f x) + (g x₀ - g x)| ≤ |f x₀ - f x| + |g x₀ - g x| :=
    abs_add_le _ _
  have hrew : (f x₀ + g x₀) - (f x + g x) = (f x₀ - f x) + (g x₀ - g x) := by ring
  rw [hrew]
  nlinarith

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: the product of two continuous real-valued maps is continuous. -/
theorem continuous_mul_real_5_12 (f g : X → ℝ)
  (hf : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) f)
  (hg : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) g) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ f x * g x) := by
  rw [continuous_iff_eps_5_9] at hf hg ⊢
  intro x₀ ε εpos
  set M : ℝ := |f x₀| + |g x₀| + 1 with hM
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  set η : ℝ := min 1 (ε / (2 * M)) with hη
  have hηpos : 0 < η := by
    rw [hη]
    apply lt_min
    · exact zero_lt_one
    · positivity
  rcases hf x₀ η hηpos with ⟨δf, δfpos, hδf⟩
  rcases hg x₀ η hηpos with ⟨δg, δgpos, hδg⟩
  refine ⟨min δf δg, by positivity, ?_⟩
  intro x hx
  have hfx : |f x₀ - f x| < η := by
    simpa [Real.dist_eq] using hδf x (lt_of_lt_of_le hx (min_le_left _ _))
  have hgx : |g x₀ - g x| < η := by
    simpa [Real.dist_eq] using hδg x (lt_of_lt_of_le hx (min_le_right _ _))
  change |f x₀ * g x₀ - f x * g x| < ε
  have hηle1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  have hηle : η ≤ ε / (2 * M) := by rw [hη]; exact min_le_right _ _
  have hgabs : |g x| < |g x₀| + 1 := by
    have : |g x - g x₀| < 1 := by
      have htmp : |g x₀ - g x| < η := hgx
      have hsymm : |g x - g x₀| = |g x₀ - g x| := by rw [abs_sub_comm]
      rw [hsymm]
      exact lt_of_lt_of_le htmp hηle1
    have htri : |g x| ≤ |g x - g x₀| + |g x₀| := by
      have := abs_add_le (g x - g x₀) (g x₀)
      simpa [sub_add_cancel] using this
    nlinarith
  have hbound1 : |f x₀| * |g x₀ - g x| ≤ |f x₀| * η := by
    gcongr
  have hbound2 : |g x| * |f x₀ - f x| < (|g x₀| + 1) * η := by
    have hnonneg1 : 0 ≤ |g x| := abs_nonneg _
    have hnonneg2 : 0 ≤ |f x₀ - f x| := abs_nonneg _
    nlinarith [hfx, hgabs]
  have habs :
      |f x₀ * (g x₀ - g x) + g x * (f x₀ - f x)|
        ≤ |f x₀ * (g x₀ - g x)| + |g x * (f x₀ - f x)| := abs_add_le _ _
  have hmul1 : |f x₀ * (g x₀ - g x)| = |f x₀| * |g x₀ - g x| := by rw [abs_mul]
  have hmul2 : |g x * (f x₀ - f x)| = |g x| * |f x₀ - f x| := by rw [abs_mul]
  have hrew : f x₀ * g x₀ - f x * g x = f x₀ * (g x₀ - g x) + g x * (f x₀ - f x) := by ring
  rw [hrew]
  have hmain :
      |f x₀ * (g x₀ - g x) + g x * (f x₀ - f x)| < ε := by
    rw [hmul1, hmul2] at habs
    have hMη : M * η ≤ ε / 2 := by
      have hnonnegM : 0 ≤ M := le_of_lt hMpos
      have hnonnegη : 0 ≤ η := le_of_lt hηpos
      have := mul_le_mul_of_nonneg_left hηle hnonnegM
      have htwo : M * (ε / (2 * M)) = ε / 2 := by
        field_simp [hMpos.ne']
      rw [htwo] at this
      exact this
    have hsum : |f x₀| * η + (|g x₀| + 1) * η ≤ ε / 2 := by
      have hsum' : |f x₀| * η + (|g x₀| + 1) * η = M * η := by
        rw [hM]
        ring
      rw [hsum']
      exact hMη
    have hA : |f x₀| * |g x₀ - g x| + |g x| * |f x₀ - f x| < ε := by
      have hlt1 : |f x₀| * |g x₀ - g x| + |g x| * |f x₀ - f x|
          < |f x₀| * η + (|g x₀| + 1) * η := by
        nlinarith [hbound1, hbound2]
      linarith [hsum, εpos]
    exact lt_of_le_of_lt habs hA
  exact hmain

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: Euclidean addition is continuous. -/
theorem continuous_add_5_12 :
    IsContinuous_5_1 (@inducedTopology_1_17 (E 2) (euclideanDistanceSpace_1_12 2))
      (@inducedTopology_1_17 ℝ inferInstance)
      (λ x : E 2 ↦ x ⟨0, by decide⟩ + x ⟨1, by decide⟩) := by
  have hcoords := (continuous_into_euclidean_5_10 (X := E 2) (f := id)).mp
    (id_continuous_5_2 (X := E 2)
      (𝒪₁ := @inducedTopology_1_17 (E 2) (euclideanDistanceSpace_1_12 2)))
  exact continuous_add_real_5_12 _ _ (hcoords ⟨0, by decide⟩) (hcoords ⟨1, by decide⟩)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: Euclidean multiplication is continuous. -/
theorem continuous_mul_5_12 :
    IsContinuous_5_1 (@inducedTopology_1_17 (E 2) (euclideanDistanceSpace_1_12 2))
      (@inducedTopology_1_17 ℝ inferInstance)
      (λ x : E 2 ↦ x ⟨0, by decide⟩ * x ⟨1, by decide⟩) := by
  have hcoords := (continuous_into_euclidean_5_10 (X := E 2) (f := id)).mp
    (id_continuous_5_2 (X := E 2)
      (𝒪₁ := @inducedTopology_1_17 (E 2) (euclideanDistanceSpace_1_12 2)))
  exact continuous_mul_real_5_12 _ _ (hcoords ⟨0, by decide⟩) (hcoords ⟨1, by decide⟩)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: powers of a continuous real-valued map are continuous. -/
theorem continuous_pow_real_5_12 (f : X → ℝ) (n : ℕ)
  (hf : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) f) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ (f x) ^ n) := by
  induction n with
  | zero =>
      simpa using constantMap_continuous_5_3
        (h𝒪₁ := inducedTopology_isTopology_1_17) (f := fun _ : X ↦ (1 : ℝ)) ⟨1, fun _ ↦ rfl⟩
  | succ n ih =>
      simpa [pow_succ', mul_comm] using continuous_mul_real_5_12 _ _ hf ih

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.12: composing a continuous real-valued map
  with a real polynomial preserves continuity. -/
theorem continuous_polynomial_real_5_12 (f : X → ℝ) (p : Polynomial ℝ)
  (hf : IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
    (@inducedTopology_1_17 ℝ inferInstance) f) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ p.eval (f x)) := by
  have hconst : ∀ a : ℝ,
      IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
        (@inducedTopology_1_17 ℝ inferInstance) (λ _ : X ↦ a) := by
    intro a
    exact constantMap_continuous_5_3
      (h𝒪₁ := inducedTopology_isTopology_1_17)
      (f := fun _ : X ↦ a) ⟨a, fun _ ↦ rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [Polynomial.eval_add] using continuous_add_real_5_12 _ _ hp hq
  | monomial n a =>
      simpa [Polynomial.eval_monomial] using
        continuous_mul_real_5_12 _ _ (hconst a) (continuous_pow_real_5_12 f n hf)

end MetricPart

section TopologyPart

variable {X : Type u} {Y : Type v}
variable {𝒪₁ : Set (Set X)} {𝒪₂ : Set (Set Y)}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.13(1a): the zero-set of a continuous real-valued map is closed. -/
theorem continuous_real_zeroSet_5_13 (f : X → ℝ)
  (hf : IsContinuous_5_1 𝒪₁ (@inducedTopology_1_17 ℝ inferInstance) f) :
    IsClosed_1_2 𝒪₁ {x : X | f x = 0} := by
  topo_auto 𝒪₂ h𝒪₂ for ℝ := @inducedTopology_1_17 ℝ inferInstance
  suffices IsClosed_1_2 𝒪₁ (f ⁻¹' {0})
    from by
      simpa only [Set.preimage, Set.mem_setOf_eq] using this
  have : IsClosed_1_2 𝒪₂ {0} := by
    have hball : closedBall_1_14 (0 : ℝ) 0 = ({0} : Set ℝ) := by
      ext x
      constructor
      · intro hx
        have h0 : DistanceSpace_1_12.dist 0 x = 0 :=
          le_antisymm hx (DistanceSpace_1_12.nonneg 0 x)
        exact (dist_eq_zero.mp h0).symm
      · intro hx
        subst x
        exact (dist_eq_zero.mpr rfl).le
    rw [← hball]
    simpa [𝒪₂] using (closedBall_closed_1_16 (x := (0 : ℝ)) (r := 0))
  exact continuous_iff_preimage_closed_5_4 f
    |>.mp hf {0} this

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.13(1b):
  the nonnegative superlevel set of a continuous real-valued map is closed. -/
theorem continuous_real_nonnegSet_5_13 (f : X → ℝ)
  (hf : IsContinuous_5_1 𝒪₁ (@inducedTopology_1_17 ℝ inferInstance) f) :
    IsClosed_1_2 𝒪₁ {x : X | 0 ≤ f x} := by
  topo_auto 𝒪₂ h𝒪₂ for ℝ := @inducedTopology_1_17 ℝ inferInstance
  suffices f ⁻¹' {y | 0 ≤ y} |> IsClosed_1_2 𝒪₁
    from by
      simpa only [Set.preimage, Set.mem_setOf_eq] using this
  have : IsClosed_1_2 𝒪₂ {y | 0 ≤ y} := by
    change IsClosed_1_2 (@inducedTopology_1_17 ℝ inferInstance) {y | 0 ≤ y}
    rw [IsClosed_1_2, inducedTopology_1_17]
    have hcompl : ({y : ℝ | 0 ≤ y}ᶜ) = {y : ℝ | y < 0} := by
      ext y
      simp
    rw [hcompl]
    intro y hy
    have hr : 0 < -y / 2 := by
      have hy' : y < 0 := hy
      have : 0 < -y := by linarith
      nlinarith
    refine ⟨-y / 2, hr, ?_⟩
    intro z hz
    have hz' : |y - z| < -y / 2 := by
      simpa [openBall_1_14, Real.dist_eq] using hz
    have habs := abs_lt.mp hz'
    have hlt : z < 0 := by
      linarith
    exact hlt
  exact continuous_iff_preimage_closed_5_4 f
    |>.mp hf {y | 0 ≤ y} this

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.13(2): strict positive superlevel sets of a continuous real-valued map are open. -/
theorem continuous_real_openSet_5_13 (f : X → ℝ)
  (hf : IsContinuous_5_1 𝒪₁ (@inducedTopology_1_17 ℝ inferInstance) f) :
    {x : X | 0 < f x} ∈ 𝒪₁ := by
  topo_auto 𝒪₂ h𝒪₂ for ℝ := @inducedTopology_1_17 ℝ inferInstance
  suffices f ⁻¹' {y | 0 < y} ∈ 𝒪₁
    from by
      simpa only [Set.preimage, Set.mem_setOf_eq] using this
  have : {y | 0 < y} ∈ 𝒪₂ := by
    change {y | 0 < y} ∈ @inducedTopology_1_17 ℝ inferInstance
    rw [inducedTopology_1_17]
    change isOpenDistance_1_15 (Set.Ioi 0)
    intro y hy
    have hr : 0 < y / 2 := by
      have hy' : 0 < y := hy
      nlinarith
    refine ⟨y / 2, hr, ?_⟩
    intro z hz
    have : |y - z| < y / 2 := by
      simpa [openBall_1_14, Real.dist_eq] using hz
    have hz' := abs_lt.mp this
    have hgt : 0 < z := by
      linarith
    exact hgt
  exact mem_preimage.mp (hf {y | 0 < y} this)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.14(1): finite conjunctions of closed polynomial inequalities and equations
  define closed sets in Euclidean space. -/
theorem euclidean_semialgebraic_basic_closed_5_14 {n : ℕ}
  (I J : Finset ℕ) (f : ℕ → E n → ℝ)
  (hf : ∀ k : ℕ,
    IsContinuous_5_1 (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n))
      (@inducedTopology_1_17 ℝ inferInstance) (f k)) :
    IsClosed_1_2 (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n))
      {x : E n | (∀ i ∈ I, 0 ≤ f i x) ∧ (∀ j ∈ J, f j x = 0)} := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 5.14(2): finite conjunctions of strict polynomial inequalities
  define open sets in Euclidean space. -/
theorem euclidean_semialgebraic_basic_open_5_14 {n : ℕ}
  (I : Finset ℕ) (f : ℕ → E n → ℝ)
  (hf : ∀ k : ℕ,
    IsContinuous_5_1 (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n))
      (@inducedTopology_1_17 ℝ inferInstance) (f k)) :
    {x : E n | ∀ i ∈ I, 0 < f i x} ∈
      (@inducedTopology_1_17 (E n) (euclideanDistanceSpace_1_12 n)) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.15: continuity may be tested on a subbasis of the codomain. -/
theorem continuous_iff_subbasis_5_15
  (h𝒪₂ : IsTopology_1_1 Y 𝒪₂) {𝒮 : Set (Set Y)}
    (h𝒮 : IsTopologicalSubbasis_3_13 𝒪₂ 𝒮) (f : X → Y) :
      IsContinuous_5_1 𝒪₁ 𝒪₂ f
        <-> ∀ S : Set Y, S ∈ 𝒮 -> f ⁻¹' S ∈ 𝒪₁ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.16: continuity is equivalent to the closure-image and closure-preimage criteria. -/
theorem continuous_iff_closure_5_16
  (h𝒪₁ : IsTopology_1_1 X 𝒪₁) (h𝒪₂ : IsTopology_1_1 Y 𝒪₂) (f : X → Y) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f
      <->
        (∀ A : Set X, f '' (closure_4_1 𝒪₁ A) ⊆ closure_4_1 𝒪₂ (f '' A)) ∧
          (∀ B : Set Y, closure_4_1 𝒪₁ (f ⁻¹' B) ⊆ f ⁻¹' closure_4_1 𝒪₂ B) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.17: continuity at a point preserves sequential convergence. -/
theorem tendstoSeq_image_of_continuousAt_5_17
  {f : X → Y} {xₙ : Sequence_2_16 X} {x : X}
  (hxₙ : TendstoSeq_2_16 𝒪₁ xₙ x)
  (hf : IsContinuousAt_5_6 𝒪₁ 𝒪₂ f x) :
    TendstoSeq_2_16 𝒪₂ (fun n : ℕ ↦ f (xₙ n)) (f x) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.18: on a first-countable domain, continuity at a point is equivalent to sequential continuity. -/
theorem continuousAt_iff_tendstoSeq_5_18
  (hFirst : FirstCountable_2_12 𝒪₁) {f : X → Y} {x : X} :
    IsContinuousAt_5_6 𝒪₁ 𝒪₂ f x
      <->
        ∀ xₙ : Sequence_2_16 X, TendstoSeq_2_16 𝒪₁ xₙ x ->
          TendstoSeq_2_16 𝒪₂ (fun n : ℕ ↦ f (xₙ n)) (f x) := by
  sorry

end TopologyPart

section MetricSequentialPart

variable {X : Type u} {Y : Type v}
variable [DistanceSpace_1_12 X] [DistanceSpace_1_12 Y]

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.19: for maps between distance spaces, continuity at a point is equivalent to sequential continuity. -/
theorem continuousAt_iff_tendstoSeq_metric_5_19
  {f : X → Y} {x : X} :
    IsContinuousAt_5_6 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›) f x
        <->
          ∀ xₙ : Sequence_2_16 X,
            TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ x ->
              TendstoSeq_2_16 (@inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›)
                (λ n : ℕ ↦ f (xₙ n)) (f x) := by
  sorry

end MetricSequentialPart

section HomeomorphismPart

variable {X : Type u} {Y : Type v}
variable {𝒪₁ : Set (Set X)} {𝒪₂ : Set (Set Y)}

/-!
Definition 5.20 introduces homeomorphisms.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 5.20: a homeomorphism is a continuous bijection with continuous inverse. -/
structure IsHomeomorphism_5_20 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) where
  toFun : X → Y
  invFun : Y → X
  continuous_toFun : IsContinuous_5_1 𝒪₁ 𝒪₂ toFun
  continuous_invFun : IsContinuous_5_1 𝒪₂ 𝒪₁ invFun
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

end HomeomorphismPart

/-!
The final statements verify that our continuity language agrees with mathlib's
bundled topological notions.
-/

open Filter Topology

section CertifyMathlib

variable {X : Type u} {Y : Type v}
variable (T₁ : TopologicalSpace X) (T₂ : TopologicalSpace Y)

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our continuity definition agrees with mathlib's `Continuous`. -/
theorem isContinuous_iff_mathlibContinuous_cert (f : X → Y) :
    IsContinuous_5_1
      {U : Set X | @IsOpen X T₁ U}
      {V : Set Y | @IsOpen Y T₂ V} f
        <-> Continuous f := by
  constructor
  · intro hf
    rw [continuous_def]
    intro V hV
    exact hf V hV
  · intro hf
    rw [continuous_def] at hf
    intro V hV
    exact hf V hV

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our pointwise continuity definition agrees with mathlib's `ContinuousAt`. -/
theorem isContinuousAt_iff_mathlibContinuousAt_cert (f : X → Y) (x : X) :
    IsContinuousAt_5_6
      {U : Set X | @IsOpen X T₁ U}
      {V : Set Y | @IsOpen Y T₂ V} f x
        <-> ContinuousAt f x := by
  constructor
  · intro hf
    rw [ContinuousAt]
    intro V hV
    have hV' : IsNeighborhood_2_1 {V : Set Y | @IsOpen Y T₂ V} (f x) V :=
      (isNeighborhood_iff_mem_nhds_cert T₂ (f x) V).2 hV
    rcases hf V hV' with ⟨U, hU, hUV⟩
    change f ⁻¹' V ∈ 𝓝 x
    exact Filter.mem_of_superset
      ((isNeighborhood_iff_mem_nhds_cert T₁ x U).1 hU) hUV
  · intro hf V hV
    have hV' : V ∈ 𝓝 (f x) :=
      (isNeighborhood_iff_mem_nhds_cert T₂ (f x) V).1 hV
    have hpre : f ⁻¹' V ∈ 𝓝 x := hf.preimage_mem_nhds hV'
    refine ⟨f ⁻¹' V, ?_, Subset.rfl⟩
    exact (isNeighborhood_iff_mem_nhds_cert T₁ x (f ⁻¹' V)).2 hpre

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our homeomorphism structure converts to mathlib's `Homeomorph`. -/
def IsHomeomorphism_5_20.toMathlibHomeomorph_cert
    (h : IsHomeomorphism_5_20
      {U : Set X | @IsOpen X T₁ U}
      {V : Set Y | @IsOpen Y T₂ V}) :
    X ≃ₜ Y where
  toFun := h.toFun
  invFun := h.invFun
  left_inv := h.left_inv
  right_inv := h.right_inv
  continuous_toFun :=
    (isContinuous_iff_mathlibContinuous_cert T₁ T₂ h.toFun).mp h.continuous_toFun
  continuous_invFun :=
    (isContinuous_iff_mathlibContinuous_cert T₂ T₁ h.invFun).mp h.continuous_invFun

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : a mathlib `Homeomorph` converts to our homeomorphism structure. -/
def Homeomorph.toArticleHomeomorphism_cert (h : X ≃ₜ Y) :
    IsHomeomorphism_5_20
      {U : Set X | @IsOpen X T₁ U}
      {V : Set Y | @IsOpen Y T₂ V} where
  toFun := h
  invFun := h.symm
  continuous_toFun :=
    (isContinuous_iff_mathlibContinuous_cert T₁ T₂ h).mpr h.continuous
  continuous_invFun :=
    (isContinuous_iff_mathlibContinuous_cert T₂ T₁ h.symm).mpr h.symm.continuous
  left_inv := h.left_inv
  right_inv := h.right_inv

end CertifyMathlib

end ContinuousMap
end LeanTopology
