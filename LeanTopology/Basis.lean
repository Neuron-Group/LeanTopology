import LeanTopology.NeighborhoodBasis
import Mathlib.Data.PNat.Basic

/-!
# 拓扑学入门3: 基
-/

noncomputable section

open Set LeanTopology.EuclideanSpaceTopology

namespace LeanTopology
namespace Basis

universe u v

section TopologyPart

open LeanTopology.TopologicalSpace
open LeanTopology.NeighborhoodBasis

/-!
Definition 3.1 introduces a topological basis as a family of open sets that
locally refines every open set.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.1: a topological basis for the topology `𝒪`. -/
def IsTopologicalBasis_3_1 {X : Type u} (𝒪 : Set (Set X)) (ℬ : Set (Set X)) : Prop :=
  ℬ ⊆ 𝒪 ∧ ∀ U ∈ 𝒪, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U

/-!
Proposition 3.2 rewrites the basis condition as a union decomposition of every
open set.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.2: a basis is equivalent to expressing every open set as a union of basis elements. -/
theorem topologicalBasis_iff_sUnion_3_2 {X : Type u} {𝒪 ℬ : Set (Set X)} :
    IsTopologicalBasis_3_1 𝒪 ℬ <->
      ℬ ⊆ 𝒪 ∧
        ∀ U ∈ 𝒪, ∃ ℬ' : Set (Set X), ℬ' ⊆ ℬ ∧ U = ⋃₀ ℬ'
          := open Classical in by
  constructor
  · intro hyp
    use hyp.left; intro U hU
    have hyp := hyp.right U hU
    choose ℬₓ hℬₓ using hyp
    have Ueq₁ : U = ⋃ x ∈ U, ℬₓ x (by
      expose_names
      exact mem_of_subset_of_mem (λ ⦃_⦄ ↦ id) h
    ) := by
      ext y
      constructor
      · intro hy
        refine mem_iUnion.mpr ?_
        refine ⟨y, mem_iUnion.mpr ?_⟩
        refine ⟨hy, ?_⟩
        exact (hℬₓ y hy).2.1
      · intro hy
        rcases mem_iUnion.mp hy with ⟨x, hx⟩
        rcases mem_iUnion.mp hx with ⟨hxU, hyB⟩
        exact (hℬₓ x hxU).2.2 hyB
    set ℬ' : Set (Set X)
      := {B : Set X | ∃ x : X, ∃ hx : x ∈ U, B = ℬₓ x hx}
    refine ⟨ℬ', ?_, ?_⟩
    · intro B hB'
      rcases hB' with ⟨x, hxU, rfl⟩
      exact (hℬₓ x hxU).1
    · rw [Ueq₁]
      ext y
      constructor
      · intro hy
        rcases mem_iUnion.mp hy with ⟨x, hx⟩
        rcases mem_iUnion.mp hx with ⟨hxU, hyB⟩
        apply mem_sUnion.mpr
        refine ⟨ℬₓ x hxU, ?_, hyB⟩
        exact ⟨x, hxU, rfl⟩
      · intro hy
        rcases mem_sUnion.mp hy with ⟨B, hB', hyB⟩
        rcases hB' with ⟨x, hxU, rfl⟩
        exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxU, hyB⟩⟩
  · intro hyp; use hyp.left
    intro U hU x hx
    rcases hyp with ⟨_, hyp⟩
    specialize hyp U hU
    rcases hyp with ⟨ℬ', ℬ'subℬ, hℬ'⟩
    rw [hℬ'] at hx
    have : ∃ B ∈ ℬ', x ∈ B := by
      exact mem_sUnion.mp hx
    rcases this with ⟨B, hB, xinB⟩
    use B; use ℬ'subℬ hB; use xinB
    simpa [hℬ'] using subset_sUnion_of_mem hB

/-!
Example 3.3 says that the topology itself is always a basis.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.3: the whole topology forms a basis of itself. -/
theorem allOpenSets_isTopologicalBasis_3_3 {X : Type u} {𝒪 : Set (Set X)} :
    IsTopologicalBasis_3_1 𝒪 𝒪 := by
  refine ⟨(by simp only [subset_refl]), ?_⟩
  intro U hU x hx
  exact ⟨U, hU, hx, (by simp only [subset_refl])⟩ 

/-!
Example 3.4 specializes the notion of basis to distance spaces.
-/

section DistancePart

open LeanTopology.TopologicalSpace

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.4: all open balls form a basis of the induced topology of a distance space. -/
theorem distance_openBall_isTopologicalBasis_3_4 {X : Type u}
    [DistanceSpace_1_12 X] :
    IsTopologicalBasis_3_1
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      {U : Set X | ∃ x : X, ∃ r : ℝ, 0 < r ∧ U = openBall_1_14 x r} := by
  constructor
  · intro U hU
    simp only [mem_setOf_eq] at hU
    rcases hU with ⟨x, r, rpos, Ueq⟩
    have := openBall_open_1_16 x r
    rw [← Ueq] at this
    exact mem_of_subset_of_mem (λ ⦃_⦄ ↦ id) this
  · intro U hU x hx
    have : isOpenDistance_1_15 U := by
      exact ((λ _ ↦ hU) ∘ U) x
    specialize this x hx
    rcases this with ⟨r, rpos, hr⟩
    use openBall_1_14 x r; simp only [mem_setOf_eq]
    constructor
    · use x; use r
    constructor
    · simp only [openBall_1_14, mem_setOf_eq]
      rw [(DistanceSpace_1_12.D1 x x).mpr rfl]
      exact RCLike.ofReal_pos.mp rpos
    · exact hr

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.4: balls of reciprocal positive-integer radius also form a basis. -/
theorem distance_invPNatBall_isTopologicalBasis_3_4 {X : Type u}
    [DistanceSpace_1_12 X] :
    IsTopologicalBasis_3_1
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      {U : Set X | ∃ x : X, ∃ n : ℕ+, U = openBall_1_14 x (1 / (n : ℝ))} := by
  constructor
  · intro U hU
    simp only [mem_setOf_eq] at hU
    rcases hU with ⟨x, n, rfl⟩
    exact (distance_openBall_isTopologicalBasis_3_4.left) ⟨x, 1 / (n : ℝ), by positivity, rfl⟩
  · intro U hU x hx
    simp only [inducedTopology_1_17, mem_setOf_eq] at hU
    rcases hU x hx with ⟨r, rpos, hBallSubU⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
    set n' : ℕ+ := ⟨max 1 n, by simp⟩ with hn'def
    have hn' : 1 / (n' : ℝ) < r := by
      rw [hn'def]
      field_simp
      have : 1 / r < max 1 ↑n := by
        simp only [one_div, lt_sup_iff]
        grind only
      simp only [PNat.mk_coe, Nat.cast_max, Nat.cast_one, gt_iff_lt]
      exact (mul_inv_lt_iff₀ rpos).mp this
    refine ⟨openBall_1_14 x (1 / (n' : ℝ)), ?_, ?_, ?_⟩
    · exact ⟨x, n', rfl⟩
    · simp only [openBall_1_14, mem_setOf_eq]
      rw [(DistanceSpace_1_12.D1 x x).mpr rfl]
      positivity
    · refine subset_trans ?_ hBallSubU
      simp only [openBall_1_14, setOf_subset_setOf]
      intro y hy
      exact Std.lt_trans hy hn'

end DistancePart

/-!
Example 3.5 records the standard bases of Euclidean space, including a
countable rational one.
-/

section EuclideanPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.5: all Euclidean open balls form a basis. -/
theorem euclidean_openBall_isTopologicalBasis_3_5 (n : ℕ) :
    IsTopologicalBasis_3_1
      {U : Set (E n) | EuclideanSpaceTopology.isOpenEuclidean_0_6 U}
      {U : Set (E n) | ∃ x : E n, ∃ r : ℝ, 0 < r ∧ U = EuclideanSpaceTopology.openBall_0_4 x r} := by
  constructor
  · intro U hU
    simp only [mem_setOf_eq] at hU
    rcases hU with ⟨x, r, rpos, rfl⟩
    exact EuclideanSpaceTopology.isOpen_ball_0_7 x r
  · intro U hU x hx
    simp only [mem_setOf_eq] at hU
    rcases hU x hx with ⟨r, rpos, hBallSubU⟩
    refine ⟨EuclideanSpaceTopology.openBall_0_4 x r, ?_, ?_, hBallSubU⟩
    · exact ⟨x, r, rpos, rfl⟩
    · simpa [EuclideanSpaceTopology.openBall_0_4] using rpos

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.5: the open intervals form a basis of `ℝ`. -/
theorem real_openInterval_isTopologicalBasis_3_5 :
    IsTopologicalBasis_3_1
      {U : Set ℝ | IsOpen U}
      {U : Set ℝ | ∃ a b : ℝ, a < b ∧ U = Set.Ioo a b} := by
  constructor
  · intro U hU
    simp only [mem_setOf_eq] at hU
    rcases hU with ⟨a, b, hab, rfl⟩
    simpa using (isOpen_Ioo : IsOpen (Set.Ioo a b))
  · intro U hU x hx
    simp only [mem_setOf_eq] at hU
    rcases Metric.isOpen_iff.mp hU x hx with ⟨r, rpos, hBallSubU⟩
    refine ⟨Set.Ioo (x - r) (x + r), ?_, ?_, ?_⟩
    · exact ⟨x - r, x + r, by linarith, rfl⟩
    · exact ⟨by linarith, by linarith⟩
    · intro y hy
      apply hBallSubU
      have hy' : |y - x| < r := by
        rw [abs_lt]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      simpa [Metric.ball, Real.dist_eq] using hy'

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.5: the rational reciprocal-radius ball family in `ℝ^n`. -/
def rationalInvPNatBallBasis_3_5 (n : ℕ) : Set (Set (E n)) :=
  {U : Set (E n) |
    ∃ x : E n, (∀ i : Fin n, ∃ q : ℚ, x i = (q : ℝ)) ∧
      ∃ k : ℕ+, U = EuclideanSpaceTopology.openBall_0_4 x (1 / (2 * (k : ℝ)))}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.5: Euclidean space admits a countable rational basis. -/
theorem rationalInvPNatBall_isTopologicalBasis_3_5 (n : ℕ) :
    IsTopologicalBasis_3_1
      {U : Set (E n) | EuclideanSpaceTopology.isOpenEuclidean_0_6 U}
      (rationalInvPNatBallBasis_3_5 n) := by
  let ratPoint : (Fin n → ℚ) → E n := fun q ↦ WithLp.toLp 2 (fun i ↦ (q i : ℝ))
  have hRatDense : DenseRange ratPoint := by
    let p : ENNReal := 2
    let emb : (Fin n → ℝ) → E n := fun f ↦ WithLp.toLp 2 f
    let coordMap : (Fin n → ℚ) → (Fin n → ℝ) := Pi.map (fun _ : Fin n ↦ (fun q : ℚ ↦ (q : ℝ)))
    let β : Fin n → Type := fun _ ↦ ℝ
    have hEmbDense : DenseRange emb := by
      rw [DenseRange]
      have hrange : Set.range emb = (Set.univ : Set (E n)) := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          refine ⟨x.ofLp, ?_⟩
          ext i
          rfl
      simp only [hrange, dense_univ]
    have hPiDense : DenseRange coordMap := by
      simpa [coordMap] using
        (DenseRange.piMap
          (ι := Fin n)
          (f := λ _ : Fin n ↦ (λ q : ℚ ↦ (q : ℝ)))
          λ _ ↦ Rat.denseRange_cast)
    have hContEmb : Continuous emb := by
      simpa [emb] using
        ((PiLp.homeomorph p β).symm.continuous)
    have hComp : DenseRange (emb ∘ coordMap) := hEmbDense.comp hPiDense hContEmb
    simpa [ratPoint, emb, coordMap] using hComp
  constructor
  · intro U hU
    rcases hU with ⟨x, _, k, rfl⟩
    exact EuclideanSpaceTopology.isOpen_ball_0_7 x (1 / (2 * (k : ℝ)))
  · intro U hU x hx
    simp only [mem_setOf_eq] at hU
    rcases hU x hx with ⟨r, rpos, hBallSubU⟩
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
    set k : ℕ+ := ⟨max 1 m, by simp⟩ with hkdef
    have hk : 1 / (k : ℝ) < r := by
      have hkpos : 0 < (k : ℝ) := by positivity
      have hm' : 1 / r < (k : ℝ) := by
        have hle : (m : ℝ) ≤ (k : ℝ) := by
          rw [hkdef]
          exact_mod_cast le_max_right 1 m
        exact lt_of_lt_of_le hm hle
      exact (one_div_lt hkpos rpos).2 hm'
    have hspos : 0 < (1 / (2 * (k : ℝ)) : ℝ) := by positivity
    have hOpenBall : IsOpen (EuclideanSpaceTopology.openBall_0_4 x (1 / (2 * (k : ℝ)))) := by
      rw [← EuclideanSpaceTopology.isOpenEuclidean_iff_isOpen_0_6]
      exact EuclideanSpaceTopology.isOpen_ball_0_7 x (1 / (2 * (k : ℝ)))
    have hNonemptyBall : (EuclideanSpaceTopology.openBall_0_4 x (1 / (2 * (k : ℝ)))).Nonempty := by
      refine ⟨x, ?_⟩
      simp only [openBall_0_4, one_div, mul_inv_rev,
        mem_setOf_eq, dist_self, inv_pos, Nat.cast_pos,
        PNat.pos, mul_pos_iff_of_pos_left, Nat.ofNat_pos]
    obtain ⟨q, hqx⟩ := hRatDense.exists_mem_open hOpenBall hNonemptyBall
    refine ⟨EuclideanSpaceTopology.openBall_0_4 (ratPoint q) (1 / (2 * (k : ℝ))), ?_, ?_, ?_⟩
    · refine ⟨ratPoint q, ?_, k, rfl⟩
      intro i
      exact ⟨q i, by
        change (fun j ↦ (q j : ℝ)) i = (q i : ℝ)
        rfl⟩
    · simpa [EuclideanSpaceTopology.openBall_0_4, EuclideanSpaceTopology.dist_comm_0_3] using hqx
    · intro y hy
      apply hBallSubU
      have hy' : dist y x < r := by
        have h1 : dist y (ratPoint q) < 1 / (2 * (k : ℝ)) := hy
        have h2 : dist (ratPoint q) x < 1 / (2 * (k : ℝ)) := hqx
        have h3 : dist y x ≤ dist y (ratPoint q) + dist (ratPoint q) x :=
          EuclideanSpaceTopology.dist_triangle_0_3 y (ratPoint q) x
        have h4 : dist y (ratPoint q) + dist (ratPoint q) x < 1 / (k : ℝ) := by
          have hsum := add_lt_add h1 h2
          have hkhalf : (1 / (2 * (k : ℝ))) + (1 / (2 * (k : ℝ))) = 1 / (k : ℝ) := by
            ring_nf
          rwa [hkhalf] at hsum
        exact lt_of_le_of_lt h3 (lt_trans h4 hk)
      exact hy'

end EuclideanPart

/-!
Definition 3.6 introduces second countability.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.6: a space is second countable if it admits a countable basis. -/
def SecondCountable_3_6 {X : Type u} (𝒪 : Set (Set X)) : Prop :=
  ∃ ℬ : Set (Set X), IsTopologicalBasis_3_1 𝒪 ℬ ∧ ℬ.Countable

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.6: Euclidean space is second countable. -/
theorem euclideanSpace_secondCountable_3_6 (n : ℕ) :
    SecondCountable_3_6 {U : Set (E n) | EuclideanSpaceTopology.isOpenEuclidean_0_6 U} := by
  let f : (Fin n → ℚ) × ℕ+ → Set (E n) := fun p ↦
    EuclideanSpaceTopology.openBall_0_4 (WithLp.toLp 2 fun i ↦ (p.1 i : ℝ)) (1 / (2 * (p.2 : ℝ)))
  have hEq : rationalInvPNatBallBasis_3_5 n = Set.range f := by
    ext U
    constructor
    · intro hU
      rcases hU with ⟨x, hxQ, k, rfl⟩
      choose q hq using hxQ
      refine ⟨(q, k), ?_⟩
      have hx : x = WithLp.toLp 2 (fun i ↦ ((q i : ℚ) : ℝ)) := by
        ext i
        simpa using hq i
      simp [f, hx]
    · rintro ⟨⟨q, k⟩, rfl⟩
      refine ⟨WithLp.toLp 2 (fun i ↦ (q i : ℝ)), ?_, k, rfl⟩
      intro i
      exact ⟨q i, by
        change (fun j ↦ (q j : ℝ)) i = (q i : ℝ)
        rfl⟩
  refine ⟨rationalInvPNatBallBasis_3_5 n, rationalInvPNatBall_isTopologicalBasis_3_5 n, ?_⟩
  rw [hEq]
  exact Set.countable_range f

/-!
Proposition 3.7 derives first countability from second countability.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.7: every second-countable space is first countable. -/
theorem secondCountable_implies_firstCountable_3_7 {X : Type u} {𝒪 : Set (Set X)} :
  SecondCountable_3_6 𝒪 -> FirstCountable_2_12 𝒪 := by
    intro hyp
    rcases hyp with ⟨ℬ, hℬ, ℬctb⟩
    rcases hℬ with ⟨ℬop, hℬ⟩
    intro x
    set ℬₓ : Set (Set X) := {B ∈ ℬ | x ∈ B}
      with ℬₓdf
    use ℬₓ; constructor
    · refine {
        isNeighborhood := ?_,
        hasRefinement := ?_ }
      · intro U hU
        rcases hU with ⟨hUℬ, hxU⟩
        exact ⟨U, ℬop hUℬ, hxU, subset_rfl⟩
      · intro V hV
        rcases hV with ⟨U, hU𝒪, hxU, hUsubV⟩
        rcases hℬ U hU𝒪 x hxU with ⟨B, hBℬ, hxB, hBsubU⟩
        refine ⟨B, ?_, subset_trans hBsubU hUsubV⟩
        exact ⟨hBℬ, hxB⟩
    · have hsub : ℬₓ ⊆ ℬ := by
        intro B hB
        exact hB.1
      exact ℬctb.mono hsub

/-!
Example 3.8 gives a standard first-countable but non-second-countable space.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.8: every discrete space is first countable. -/
theorem discreteSpace_firstCountable_3_8 {X : Type u} :
    FirstCountable_2_12 (discreteTopology_1_6 X) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.8: an uncountable discrete space is not second countable. -/
theorem uncountable_discrete_not_secondCountable_3_8 {X : Type u}
    (hX : ¬ Set.Countable (univ : Set X)) :
    ¬ SecondCountable_3_6 (discreteTopology_1_6 X) := by
  sorry

/-!
Proposition 3.9 extracts the topology-free properties `OB1` and `OB2` of a
basis.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.9: the abstract properties of a basis family. -/
structure IsTopologicalBasisFamily_3_9 (X : Type u) (ℬ : Set (Set X)) : Prop where
  OB1_mem : ∀ x : X, ∃ B ∈ ℬ, x ∈ B
  OB2_inter : ∀ ⦃B₁ B₂ : Set X⦄, B₁ ∈ ℬ → B₂ ∈ ℬ → ∀ ⦃x : X⦄, x ∈ B₁ ∩ B₂ →
    ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B₁ ∩ B₂

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.9: every basis satisfies `OB1` and `OB2`. -/
theorem topologicalBasis_properties_3_9 {X : Type u} {𝒪 ℬ : Set (Set X)}
    (h𝒪 : IsTopology_1_1 X 𝒪) (hℬ : IsTopologicalBasis_3_1 𝒪 ℬ) :
    IsTopologicalBasisFamily_3_9 X ℬ := by
  sorry

/-!
Proposition 3.10 reconstructs a topology from a family satisfying `OB1` and
`OB2`.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.10: the topology generated by a prescribed basis family. -/
def topologyFromTopologicalBasis_3_10 {X : Type u} (ℬ : Set (Set X)) : Set (Set X) :=
  {U : Set X | ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.10: the generated topology, its basis property, and uniqueness. -/
structure BasisTopologyData_3_10 {X : Type u} (ℬ : Set (Set X)) : Prop where
  isTopology :
    IsTopology_1_1 X (topologyFromTopologicalBasis_3_10 ℬ)
  isBasis :
    IsTopologicalBasis_3_1 (topologyFromTopologicalBasis_3_10 ℬ) ℬ
  unique :
    ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 →
      IsTopologicalBasis_3_1 𝒪 ℬ →
        𝒪 = topologyFromTopologicalBasis_3_10 ℬ

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.10: `OB1` and `OB2` generate a unique topology. -/
theorem topology_from_topologicalBasis_3_10 {X : Type u} [Nonempty X] {ℬ : Set (Set X)}
    (hℬ : IsTopologicalBasisFamily_3_9 X ℬ) :
    BasisTopologyData_3_10 ℬ := by
  sorry

/-!
Remark 3.11 records the minimality of the topology generated by a basis.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 3.11: the topology generated by a basis is the smallest topology containing it. -/
theorem topologyFromTopologicalBasis_minimal_3_11 {X : Type u} [Nonempty X]
    {ℬ : Set (Set X)} (hℬ : IsTopologicalBasisFamily_3_9 X ℬ) :
    ℬ ⊆ topologyFromTopologicalBasis_3_10 ℬ ∧
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 → ℬ ⊆ 𝒪 →
        topologyFromTopologicalBasis_3_10 ℬ ⊆ 𝒪 := by
  sorry

/-!
Example 3.12 introduces the Sorgenfrey line and its basic properties.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.12: the half-open interval basis of the Sorgenfrey line. -/
def SorgenfreyBasis_3_12 : Set (Set ℝ) :=
  {U : Set ℝ | ∃ a b : ℝ, a < b ∧ U = Set.Ico a b}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.12: the half-open intervals satisfy `OB1` and `OB2`. -/
theorem SorgenfreyBasis_properties_3_12 :
    IsTopologicalBasisFamily_3_9 ℝ SorgenfreyBasis_3_12 := by
  sorry

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.12: the topology generated by the Sorgenfrey basis. -/
def SorgenfreyTopology_3_12 : Set (Set ℝ) :=
  topologyFromTopologicalBasis_3_10 SorgenfreyBasis_3_12

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.12: the intervals `[x, x + 1/n)` form a neighborhood basis in the Sorgenfrey line. -/
theorem Sorgenfrey_intervalNeighborhoodBasis_3_12 (x : ℝ) :
    IsNeighborhoodBasis_2_5 SorgenfreyTopology_3_12 x
      {U : Set ℝ | ∃ n : ℕ+, U = Set.Ico x (x + 1 / (n : ℝ))} := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.12: the Sorgenfrey line is first countable. -/
theorem Sorgenfrey_firstCountable_3_12 :
    FirstCountable_2_12 SorgenfreyTopology_3_12 := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.12: the Sorgenfrey line is not second countable. -/
theorem Sorgenfrey_not_secondCountable_3_12 :
    ¬ SecondCountable_3_6 SorgenfreyTopology_3_12 := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.12: the usual Euclidean topology on `ℝ` is contained in the Sorgenfrey topology. -/
theorem euclideanTopology_subset_sorgenfreyTopology_3_12 :
    {U : Set ℝ | IsOpen U} ⊆ SorgenfreyTopology_3_12 := by
  sorry

/-!
Definition 3.13 weakens a basis to a subbasis by taking finite intersections.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.13: the family of nonempty finite intersections of elements of `𝒮`. -/
def finiteIntersections_3_13 {X : Type u} (𝒮 : Set (Set X)) : Set (Set X) :=
  {B : Set X |
    ∃ 𝒜 : Finset (Set X), 𝒜.Nonempty ∧
      (∀ S ∈ 𝒜, S ∈ 𝒮) ∧ B = ⋂₀ (↑𝒜 : Set (Set X))}

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.13: a subbasis is a family whose finite intersections form a basis. -/
def IsTopologicalSubbasis_3_13 {X : Type u} (𝒪 : Set (Set X)) (𝒮 : Set (Set X)) : Prop :=
  IsTopologicalBasis_3_1 𝒪 (finiteIntersections_3_13 𝒮)

/-- ℛℯ𝓂𝒶𝓇𝓀 3.13: every basis may also be regarded as a subbasis. -/
theorem topologicalBasis_isTopologicalSubbasis_3_13 {X : Type u} {𝒪 ℬ : Set (Set X)}
    (hℬ : IsTopologicalBasis_3_1 𝒪 ℬ) :
    IsTopologicalSubbasis_3_13 𝒪 ℬ := by
  sorry

/-!
Example 3.14 gives the standard ray subbasis of the real line.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.14: the ray family on `ℝ`. -/
def realRaySubbasis_3_14 : Set (Set ℝ) :=
  {U : Set ℝ | ∃ a : ℝ, U = Set.Ioi a} ∪
    {U : Set ℝ | ∃ b : ℝ, U = Set.Iio b}

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 3.14: the open rays form a subbasis of the usual topology on `ℝ`. -/
theorem realRay_isTopologicalSubbasis_3_14 :
    IsTopologicalSubbasis_3_13
      {U : Set ℝ | IsOpen U}
      realRaySubbasis_3_14 := by
  sorry

/-!
Proposition 3.15 extracts the very weak covering property of a subbasis.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.15: the abstract covering property of a subbasis family. -/
structure IsTopologicalSubbasisFamily_3_15 (X : Type u) (𝒮 : Set (Set X)) : Prop where
  SB_cover : ∀ x : X, ∃ S ∈ 𝒮, x ∈ S

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.15: every subbasis satisfies the covering property `SB`. -/
theorem topologicalSubbasis_property_3_15 {X : Type u} {𝒪 𝒮 : Set (Set X)}
    (h𝒮 : IsTopologicalSubbasis_3_13 𝒪 𝒮) :
    IsTopologicalSubbasisFamily_3_15 X 𝒮 := by
  sorry

/-!
Proposition 3.16 reconstructs a topology from any family satisfying the weak
covering condition `SB`.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 3.16: the topology generated by a subbasis. -/
def topologyFromTopologicalSubbasis_3_16 {X : Type u} (𝒮 : Set (Set X)) : Set (Set X) :=
  topologyFromTopologicalBasis_3_10 (finiteIntersections_3_13 𝒮)

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.16: the generated topology, its subbasis property, and uniqueness. -/
structure SubbasisTopologyData_3_16 {X : Type u} (𝒮 : Set (Set X)) : Prop where
  isTopology :
    IsTopology_1_1 X (topologyFromTopologicalSubbasis_3_16 𝒮)
  isSubbasis :
    IsTopologicalSubbasis_3_13 (topologyFromTopologicalSubbasis_3_16 𝒮) 𝒮
  unique :
    ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 →
      IsTopologicalSubbasis_3_13 𝒪 𝒮 →
        𝒪 = topologyFromTopologicalSubbasis_3_16 𝒮

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 3.16: every family satisfying `SB` generates a unique topology. -/
theorem topology_from_topologicalSubbasis_3_16 {X : Type u} [Nonempty X] {𝒮 : Set (Set X)}
    (h𝒮 : IsTopologicalSubbasisFamily_3_15 X 𝒮) :
    SubbasisTopologyData_3_16 𝒮 := by
  sorry

/-!
Remark 3.17 records the minimality of the topology generated by a subbasis.
-/

/-- ℛℯ𝓂𝒶𝓇𝓀 3.17: the topology generated by a subbasis is the smallest topology containing it. -/
theorem topologyFromTopologicalSubbasis_minimal_3_17 {X : Type u} [Nonempty X]
    {𝒮 : Set (Set X)} (h𝒮 : IsTopologicalSubbasisFamily_3_15 X 𝒮) :
    𝒮 ⊆ topologyFromTopologicalSubbasis_3_16 𝒮 ∧
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 → 𝒮 ⊆ 𝒪 →
        topologyFromTopologicalSubbasis_3_16 𝒮 ⊆ 𝒪 := by
  sorry

/-!
The final certification relates the article's basis definition to mathlib's
`IsTopologicalBasis`.
-/

open Topology in
/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our basis definition agrees with mathlib's `IsTopologicalBasis`. -/
theorem isTopologicalBasis_iff_mathlib_cert {X : Type u}
    (T : TopologicalSpace X) (ℬ : Set (Set X)) :
    IsTopologicalBasis_3_1 {U : Set X | @IsOpen X T U} ℬ ↔ TopologicalSpace.IsTopologicalBasis ℬ := by
  sorry

end TopologyPart

end Basis
end LeanTopology
