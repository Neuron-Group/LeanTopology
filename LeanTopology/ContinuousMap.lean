import LeanTopology.ClosureInterior

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
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.2 (2): the composition of continuous maps is continuous. -/
theorem continuous_comp_5_2 {f : X → Y} {g : Y → Z}
  (hf : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
  (hg : IsContinuous_5_1 𝒪₂ 𝒪₃ g) :
    IsContinuous_5_1 𝒪₁ 𝒪₃ (g ∘ f) := by
  sorry

/-- A map is constant when all its values coincide with one fixed point. -/
def IsConstantMap_5_3 (f : X → Y) : Prop :=
  ∃ c : Y, ∀ x : X, f x = c

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.3: every constant map is continuous. -/
theorem constantMap_continuous_5_3 {f : X → Y}
  (hf : IsConstantMap_5_3 f) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f := by
  sorry

/-!
Proposition 5.4 rewrites continuity using closed sets.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.4: continuity is equivalent to preservation of closedness under preimages. -/
theorem continuous_iff_preimage_closed_5_4
  (h𝒪₁ : IsTopology_1_1 X 𝒪₁) (h𝒪₂ : IsTopology_1_1 Y 𝒪₂) (f : X → Y) :
    IsContinuous_5_1 𝒪₁ 𝒪₂ f
      <->
        ∀ F : Set Y, IsClosed_1_2 𝒪₂ F -> IsClosed_1_2 𝒪₁ (f ⁻¹' F) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.5 (1): every map from a discrete space is continuous. -/
theorem continuous_from_discrete_5_5 (f : X → Y) :
    IsContinuous_5_1 (discreteTopology_1_6 X) 𝒪₂ f := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.5 (2): every map into an indiscrete space is continuous. -/
theorem continuous_to_indiscrete_5_5 (f : X → Y) :
    IsContinuous_5_1 𝒪₁ (indiscreteTopology_1_7 Y) f := by
  sorry

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
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.8: continuity at a point may be tested on neighborhood bases. -/
theorem continuousAt_iff_neighborhoodBasis_5_8
    {f : X → Y} {x : X} {𝒰 : Set (Set X)} {𝒱 : Set (Set Y)}
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪₁ x 𝒰)
    (h𝒱 : IsNeighborhoodBasis_2_5 𝒪₂ (f x) 𝒱) :
    IsContinuousAt_5_6 𝒪₁ 𝒪₂ f x
      <-> ∀ V : Set Y, V ∈ 𝒱 -> ∃ U : Set X, U ∈ 𝒰 ∧ U ⊆ f ⁻¹' V := by
  sorry

end TopologyPart

section MetricPart

variable {X : Type u} {Y : Type v}
variable [DistanceSpace_1_12 X] [DistanceSpace_1_12 Y]

open LeanTopology.TopologicalSpace

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.9: the equivalent formulations of continuity for maps between distance spaces. -/
structure ContinuousMetricData_5_9 (f : X → Y) : Prop where
  topo_iff_ball :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (@inducedTopology_1_17 Y ‹DistanceSpace_1_12 Y›) f
        <->
          ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
            f '' openBall_1_14 x₀ δ ⊆ openBall_1_14 (f x₀) ε
  ball_iff_eps :
    (∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
      f '' openBall_1_14 x₀ δ ⊆ openBall_1_14 (f x₀) ε)
        <->
          ∀ x₀ : X, ∀ ε > 0, ∃ δ > 0,
            ∀ x : X, DistanceSpace_1_12.dist x₀ x < δ ->
              DistanceSpace_1_12.dist (f x₀) (f x) < ε

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.9: metric continuity is equivalent to the epsilon-delta formulations. -/
theorem continuous_metric_5_9 (f : X → Y) :
    ContinuousMetricData_5_9 f := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.10: a map into a Euclidean subspace is continuous iff each coordinate is continuous. -/
theorem continuous_into_euclidean_5_10 {n : ℕ}
    {A : Set (E n)} (f : X → A) :
    IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      (euclideanSubspaceTopology_2_21 n A) f
        <->
          ∀ i : Fin n,
            IsContinuous_5_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
              (@inducedTopology_1_17 ℝ inferInstance) (λ x : X ↦ (f x).1 i) := by
  sorry

end MetricPart

section TopologyPart

variable {X : Type u} {Y : Type v}
variable {𝒪₁ : Set (Set X)} {𝒪₂ : Set (Set Y)}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 5.13: zero-sets and superlevel sets of a continuous real-valued map are closed,
and strict superlevel sets are open. -/
theorem continuous_real_sets_5_13 (f : X → ℝ)
    (hf : IsContinuous_5_1 𝒪₁ (@inducedTopology_1_17 ℝ inferInstance) f) :
    IsClosed_1_2 𝒪₁ {x : X | f x = 0} ∧
      IsClosed_1_2 𝒪₁ {x : X | 0 ≤ f x} ∧
        {x : X | 0 < f x} ∈ 𝒪₁ := by
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
