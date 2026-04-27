import LeanTopology.Import
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic

/-!
# 拓扑学入门0: 欧几里得空间的拓扑

As a basic discipline that permeates different aspects of modern mathematics,
  topology plays an important role in notions such as "continuous", "tend to", or "approach".
This section focuses on the topological structure in Euclidean space,
  serving as a lead-in to more abstract topological notions.
-/

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace LeanTopology
namespace EuclideanSpaceTopology

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
The article starts from the usual Euclidean inner product and norm.
Mathlib already provides these as `⟪x, y⟫_ℝ` and `‖x‖` on
`EuclideanSpace ℝ (Fin n)`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.1: the Cauchy--Schwarz inequality in Euclidean space. -/
theorem cauchy_schwarz_0_1 {n : ℕ} (x y : E n) :
    (inner ℝ x y) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le x y

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.2: the triangle inequality for the Euclidean norm. -/
theorem norm_triangle_0_2 {n : ℕ} (x y : E n) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  exact norm_add_le x y

/-!
The Euclidean distance between `x` and `y` is the norm of `x - y`.
Mathlib's standard notation is `dist x y`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.3, first property: Euclidean distance vanishes exactly on equal points. -/
theorem dist_eq_zero_iff_0_3 {n : ℕ} (x y : E n) :
    dist x y = 0 ↔ x = y := by
  exact dist_eq_zero

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.3, second property: Euclidean distance is symmetric. -/
theorem dist_comm_0_3 {n : ℕ} (x y : E n) :
    dist x y = dist y x := by
  exact PseudoMetricSpace.dist_comm x y

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.3, third property: Euclidean distance satisfies the triangle inequality. -/
theorem dist_triangle_0_3 {n : ℕ} (x y z : E n) :
    dist x z ≤ dist x y + dist y z := by
  exact dist_triangle x y z

/-!
Definition 0.4 introduces open balls directly from the Euclidean distance:
`B(x, r)` is the set of points whose distance from `x` is less than `r`.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 0.4: the open ball in Euclidean space. -/
abbrev openBall_0_4 {n : ℕ} (x : E n) (r : ℝ) : Set (E n) :=
  {y : E n | dist y x < r}

/-!
The article's open ball is the same object as mathlib's standard metric ball.
-/

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our open ball equals `Metric.ball`. -/
theorem openBall_eq_metric_ball_0_4 {n : ℕ} (x : E n) (r : ℝ) :
    openBall_0_4 x r = Metric.ball x r := by
  rfl

/-- Monotonicity of the article's open balls with respect to the radius. -/
theorem openBall_mono_0_4 {n : ℕ} {x : E n} {r₁ r₂ : ℝ} :
    r₁ ≤ r₂ → openBall_0_4 x r₁ ⊆ openBall_0_4 x r₂ := by
  intro le y hy
  simp only [mem_setOf_eq] at hy ⊢
  linarith

/-!
Proposition 0.5 rewrites epsilon-delta continuity at a point using open balls:
small balls around `a` are mapped into small balls around `f a`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.5: continuity at a point described by images of open balls. -/
theorem continuousAt_iff_ball_0_5 {n m : ℕ} (f : E n → E m) (a : E n) :
    ContinuousAt f a <->
      ∀ ε > 0, ∃ δ > 0,
        f '' openBall_0_4 a δ ⊆ openBall_0_4 (f a) ε := by
  rw [ContinuousAt, Metric.tendsto_nhds_nhds]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδ_maps⟩
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hδ_maps hx
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hδ_maps⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    exact hδ_maps ⟨x, hx, rfl⟩

/-!
Definition 0.6 introduces open subsets of Euclidean space through open balls:
every point of the set must contain some open ball around it still contained
in the set.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 0.6: an open subset of Euclidean space. -/
abbrev isOpenEuclidean_0_6 {n : ℕ} (U : Set (E n)) : Prop :=
  ∀ x ∈ U, ∃ r > 0, openBall_0_4 x r ⊆ U

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our definition is equivalent to `IsOpen`. -/
theorem isOpenEuclidean_iff_isOpen_0_6 {n : ℕ} (U : Set (E n)) :
    isOpenEuclidean_0_6 U <-> IsOpen U := by
  simpa [isOpenEuclidean_0_6, openBall_eq_metric_ball_0_4] using
    (Metric.isOpen_iff (s := U)).symm

/-!
Proposition 0.7 states that every Euclidean open ball is an open set.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.7: every open ball in Euclidean space is open. -/
theorem isOpen_ball_0_7 {n : ℕ} (x : E n) (r : ℝ) :
    isOpenEuclidean_0_6 (openBall_0_4 x r) := by
  intro y yinBall
  simp only [openBall_0_4, mem_setOf_eq,
    gt_iff_lt, setOf_subset_setOf] at yinBall ⊢
  set r' := r - dist y x with r'df
  have r'pos : 0 < r' := by
    rw [r'df]
    linarith
  use r'; use r'pos; intro z hz;
  rw [dist_comm]
  have c1 : dist x z ≤ dist x y + dist y z := dist_triangle_0_3 x y z
  have c2 : dist x y + dist y z < dist x y + r' := by
    rw [dist_comm] at hz
    refine add_lt_add_right hz (dist x y)
  have c3 : dist x y + r' = r := by
    rw [dist_comm] at r'df
    rw [r'df]
    simp only [add_sub_cancel]
  linarith

/-!
Proposition 0.8 records the three basic closure properties of open sets:
the empty set and whole space are open, finite intersections are open, and
arbitrary unions are open.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.8, first property: both `∅` and the whole Euclidean space are open. -/
theorem isOpen_empty_univ_0_8 {n : ℕ} :
    isOpenEuclidean_0_6 (∅ : Set (E n)) ∧ isOpenEuclidean_0_6 (univ : Set (E n)) := by
  constructor
  · intro x xin
    exfalso
    exact (iff_false_intro λ a ↦ xin).mp xin
  · intro x xin
    use 1; use zero_lt_one;
    simp

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.8, second property: the intersection of two open sets is open. -/
theorem isOpen_inter_0_8 {n : ℕ} {U₁ U₂ : Set (E n)}
    (hU₁ : isOpenEuclidean_0_6 U₁) (hU₂ : isOpenEuclidean_0_6 U₂) :
    isOpenEuclidean_0_6 (U₁ ∩ U₂) := by
  by_cases itr_emp : U₁ ∩ U₂ = ∅
  · rw [itr_emp]
    exact isOpen_empty_univ_0_8.left
  · intro x xin
    obtain ⟨r₁, r₁pos, hr₁⟩ := hU₁ x xin.left
    obtain ⟨r₂, r₂pos, hr₂⟩ := hU₂ x xin.right
    set r := min r₁ r₂ with rdf
    have rpos : 0 < r := lt_min r₁pos r₂pos
    use r; use rpos;
    apply subset_inter
    · have : r ≤ r₁ := Std.min_le_left
      exact (openBall_mono_0_4 this).trans hr₁
    · have : r ≤ r₂ := Std.min_le_right
      exact (openBall_mono_0_4 this).trans hr₂

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 0.8, third property: an arbitrary union of open sets is open. -/
theorem isOpen_iUnion_0_8 {n : ℕ} {ι : Type*} {U : ι → Set (E n)}
    (hU : ∀ i, isOpenEuclidean_0_6 (U i)) :
    isOpenEuclidean_0_6 (⋃ i, U i) := by
  intro x hx
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hx
  specialize hU i₀ x hi₀
  rcases hU with ⟨r, rpos, hball⟩
  use r; use rpos;
  exact subset_iUnion_of_subset i₀ hball

/-!
Theorem 0.9 is the standard open-set characterization of continuity:
a map between Euclidean spaces is continuous exactly when preimages of open
sets are open.
-/

/-- 𝒯𝒽ℯℴ𝓇ℯ𝓂 0.9: continuity is equivalent to openness of all preimages. -/
theorem continuous_iff_preimage_open_0_9 {n m : ℕ} (f : E n → E m) :
    Continuous f <->
      ∀ V : Set (E m), isOpenEuclidean_0_6 V → isOpenEuclidean_0_6 (f ⁻¹' V) := by
  constructor
  · intro hf V hV
    by_cases hpre_empty : f ⁻¹' V = ∅
    · rw [hpre_empty]
      exact isOpen_empty_univ_0_8.left
    · intro a ha
      have hfa : f a ∈ V := ha
      obtain ⟨ε, hεpos, hεV⟩ := hV (f a) hfa
      obtain ⟨δ, hδpos, hδ_maps⟩ :=
        (continuousAt_iff_ball_0_5 f a).mp hf.continuousAt ε hεpos
      have hball_preimage : openBall_0_4 a δ ⊆ f ⁻¹' V := by
        intro x hx
        have hfx_ball : f x ∈ openBall_0_4 (f a) ε :=
          hδ_maps ⟨x, hx, rfl⟩
        exact hεV hfx_ball
      exact ⟨δ, hδpos, hball_preimage⟩
  · intro hpre
    rw [continuous_iff_continuousAt]
    intro a
    rw [continuousAt_iff_ball_0_5]
    intro ε hεpos
    let V : Set (E m) := openBall_0_4 (f a) ε
    have hV : isOpenEuclidean_0_6 V := isOpen_ball_0_7 (f a) ε
    have ha : a ∈ f ⁻¹' V := by
      simp [V, openBall_0_4, hεpos]
    obtain ⟨δ, hδpos, hδ_preimage⟩ := hpre V hV a ha
    have hball_preimage : openBall_0_4 a δ ⊆ f ⁻¹' V := hδ_preimage
    have himage_ball : f '' openBall_0_4 a δ ⊆ openBall_0_4 (f a) ε := by
      rintro _ ⟨x, hx, rfl⟩
      exact hball_preimage hx
    refine ⟨δ, hδpos, ?_⟩
    exact himage_ball

end EuclideanSpaceTopology
end LeanTopology
