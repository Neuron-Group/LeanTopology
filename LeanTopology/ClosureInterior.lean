import LeanTopology.NeighborhoodBasis
import LeanTopology.Basis
import Mathlib.Topology.Closure

/-!
# 拓扑学入门4: 闭包和内部

This file follows the article's development of closure, dense sets, interior,
and boundary. At this stage we mainly set up the definitions and the formal
statement skeletons, while leaving the longer proofs as `sorry`.
-/

noncomputable section

open Set

namespace LeanTopology
namespace ClosureInterior

universe u

open LeanTopology.EuclideanSpaceTopology
open LeanTopology.TopologicalSpace
open LeanTopology.NeighborhoodBasis
open LeanTopology.Basis

section TopologyPart

variable {X : Type u} {𝒪 : Set (Set X)}

/-!
Definition 4.1 introduces the closure of a subset as the intersection of all
closed supersets.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.1: the family of closed supersets of `A`. -/
def ClosedSupersets_4_1 (𝒪 : Set (Set X)) (A : Set X) : Set (Set X) :=
  {F : Set X | IsClosed_1_2 𝒪 F ∧ A ⊆ F}

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.1: the closure of `A` is the intersection of all closed supersets of `A`. -/
def closure_4_1 (𝒪 : Set (Set X)) (A : Set X) : Set X :=
  ⋂₀ ClosedSupersets_4_1 𝒪 A

/-- `A` is always contained in its closure. -/
theorem subset_closure_4_1 (A : Set X) :
    A ⊆ closure_4_1 𝒪 A := by
  intro x hx
  simp only [closure_4_1, ClosedSupersets_4_1, mem_sInter, mem_setOf_eq]
  intro F hF
  exact hF.2 hx

/-- The closure is a closed set. -/
theorem closure_isClosed_4_1 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    IsClosed_1_2 𝒪 (closure_4_1 𝒪 A) := by
  apply (closedSet_properties_1_3.mp h𝒪).C3_sInter
  intro F hF; exact hF.left

/-!
Proposition 4.2 records the minimality of closure among closed supersets.
-/
def False := ∀ A : Prop, A
def Not := λ A ↦ A -> False
def True := Not False
def delta : True := λ z ↦ z True z
def omega : Not (∀ A B : Prop, A = B) := λ h A ↦ cast (h True A) delta
def Omega : Not (∀ A B : Prop, A = B) := λ h ↦ delta (omega h)
/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.2: every closed superset of `A` contains `closure A`. -/
theorem closure_minimal_4_2 (A F : Set X)
  (hFclosed : IsClosed_1_2 𝒪 F) (hAF : A ⊆ F) :
    closure_4_1 𝒪 A ⊆ F := by
  intro x hx
  simp only [
    closure_4_1,
    ClosedSupersets_4_1,
    mem_sInter,
    mem_setOf_eq,
    and_imp
  ] at hx
  exact hx F hFclosed hAF

/-- A point of the closure belongs to every closed superset. -/
theorem closure_mem_of_closed_4_2 {A F : Set X} {x : X}
  (hFclosed : IsClosed_1_2 𝒪 F) (hAF : A ⊆ F)
    (hx : x ∈ closure_4_1 𝒪 A) :
      x ∈ F := by
  specialize hx F
  simp only [ClosedSupersets_4_1,
    mem_setOf_eq, and_imp] at hx
  specialize hx hFclosed hAF
  exact hx

/-- 𝒩ℴ𝓉ℯ 4.3: a set is closed iff it equals its closure. -/
theorem isClosed_iff_eq_closure_4_3 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
  IsClosed_1_2 𝒪 A
    <-> closure_4_1 𝒪 A = A := by
  constructor
  <;> intro hyp
  · ext x; constructor
    <;> intro hyp'
    · apply hyp' A
      unfold ClosedSupersets_4_1
      simp only [mem_setOf_eq, subset_refl, and_true];
      exact hyp
    · exact subset_closure_4_1 A hyp'
  · rw [← hyp]
    exact closure_isClosed_4_1 h𝒪 A

theorem isClosed_of_closure_subset_4_3
  (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    closure_4_1 𝒪 A ⊆ A -> IsClosed_1_2 𝒪 A := by
  intro hyp
  have hEq : closure_4_1 𝒪 A = A := Subset.antisymm hyp (subset_closure_4_1 A)
  exact (isClosed_iff_eq_closure_4_3 h𝒪 A).2 hEq

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.4: closure is monotone. -/
theorem closure_mono_4_4 {A B : Set X} (hAB : A ⊆ B) :
    closure_4_1 𝒪 A ⊆ closure_4_1 𝒪 B := by
  intro x hx
  simp only [closure_4_1, ClosedSupersets_4_1, mem_sInter, mem_setOf_eq] at hx ⊢
  intro F hF
  exact hx F ⟨hF.1, hAB.trans hF.2⟩

/-- Nonempty intersection is preserved by enlarging the right factor. -/
theorem inter_nonempty_of_subset_right_4_5 {A U V : Set X} :
  (A ∩ U).Nonempty -> U ⊆ V -> (A ∩ V).Nonempty := by
    intro hAU hUV
    rcases hAU with ⟨x, hxA, hxU⟩
    use x; use hxA; exact mem_of_subset_of_mem hUV hxU

theorem inter_empty_of_subset_right {A U V : Set X} :
  A ∩ V = ∅ -> U ⊆ V -> A ∩ U = ∅ := by
    intro hAV hUV
    ext x
    constructor <;> intro hyp
    · have : x ∈ A ∩ V := by
        constructor
        · exact hyp.left
        · exact mem_of_subset_of_mem hUV hyp.right
      exact hAV ▸ this
    · exact not_notMem.mp λ _ ↦ hyp

theorem inter_empty_iff_subset_compl_right {A U : Set X} :
  A ∩ U = ∅ <-> A ⊆ Uᶜ := by
    constructor
    · intro hAU x hxA hxU
      have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
      rw [hAU] at hx
      exact hx
    · intro hAcompl
      ext x
      constructor <;> intro hx
      · exact hAcompl hx.1 hx.2
      · exact False.elim hx

/-!
Proposition 4.5 characterizes points of the closure by neighborhoods.
-/

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: closure points are exactly those meeting every neighborhood. -/
theorem mem_closure_iff_neighborhood_4_5'
  (A : Set X) (x : X) :
    x ∈ closure_4_1 𝒪 A
      <-> ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V
        -> (A ∩ V).Nonempty := by
  constructor <;> intro hyp
  · intro V hV
    by_contra ct
    have hAV : A ∩ V = ∅
      := not_nonempty_iff_eq_empty.mp ct
    rcases hV with ⟨U, Uop, xinU, UsubV⟩
    have hAU : A ∩ U = ∅
      := inter_empty_of_subset_right hAV UsubV
    set F := Uᶜ with Fdf
    have Fcl : IsClosed_1_2 𝒪 F
      := (isClosed_compl_iff_open U).mpr Uop
    have AsubF : A ⊆ F := by
      rw [Fdf]
      exact (inter_empty_iff_subset_compl_right).mp hAU
    simp only [closure_4_1, ClosedSupersets_4_1,
      mem_sInter, mem_setOf_eq, and_imp] at hyp
    specialize hyp F Fcl AsubF
    rw [Fdf] at hyp
    contradiction
  · intro F hF; simp only [ClosedSupersets_4_1,
      mem_setOf_eq] at hF
    by_contra ct
    have xinV : x ∈ Fᶜ := (mem_compl_iff F x).mpr ct
    set V := Fᶜ with Vdf
    have Vop : V ∈ 𝒪 := by
      rw [Vdf]
      exact hF.1
    have : IsNeighborhood_2_1 𝒪 x V
      := neighborhood_of_open_mem Vop xinV
    specialize hyp V this
    rcases hF with ⟨-, hF⟩
    have hAV : A ∩ V = ∅ := by
      have hA : A ⊆ (Fᶜ)ᶜ := by
        have hFF : F = (Fᶜ)ᶜ := (compl_compl F).symm
        rw [← hFF]
        exact hF
      rw [← Vdf] at hA
      exact inter_empty_iff_subset_compl_right
        |>.mpr hA
    rw [hAV] at hyp
    rcases hyp with ⟨y, hy⟩
    exact hy

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: closure points are exactly those meeting every neighborhood. -/
theorem mem_closure_iff_neighborhood_4_5 (_h𝒪 : IsTopology_1_1 X 𝒪)
  (A : Set X) (x : X) :
    x ∈ closure_4_1 𝒪 A
      <-> ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V -> (A ∩ V).Nonempty := by
  simpa using mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough to test only open neighborhoods. -/
theorem mem_closure_iff_openNeighborhood_4_5 (h𝒪 : IsTopology_1_1 X 𝒪)
  (A : Set X) (x : X) :
    x ∈ closure_4_1 𝒪 A <->
      ∀ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V
        -> (A ∩ V).Nonempty := by
  constructor
  · intro hx V Vop
    exact mem_closure_iff_neighborhood_4_5 h𝒪 A x
      |>.mp hx V Vop.left
  · intro hyp
    /- Same with the precede,
      Since neighborhood in precede is exactly open. -/
    refine (mem_closure_iff_neighborhood_4_5 h𝒪 A x).2 ?_
    intro V hV
    rcases hV with ⟨U, Uop, xinU, UsubV⟩
    exact inter_nonempty_of_subset_right_4_5
      (hyp U ⟨neighborhood_of_open_mem Uop xinU, Uop⟩) UsubV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough to test one neighborhood basis. -/
theorem mem_closure_iff_neighborhoodBasis_4_5 (h𝒪 : IsTopology_1_1 X 𝒪)
  (A : Set X) (x : X) (𝒰 : Set (Set X))
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰) :
      x ∈ closure_4_1 𝒪 A
        <-> ∀ V ∈ 𝒰, (A ∩ V).Nonempty := by
  constructor
  · intro hx V hV
    have := h𝒰.isNeighborhood V hV
    exact mem_closure_iff_neighborhood_4_5 h𝒪 A x
      |>.mp hx V this
  · intro hyp
    /-
      Simular with precedes.
      Which means you could find V,
        satisfied x ∈ V ∈ 𝒰
          and V is a subset of previous openneighborhood.
    -/
    refine (mem_closure_iff_neighborhood_4_5 h𝒪 A x).2 ?_
    intro V hV
    rcases h𝒰.hasRefinement V hV with ⟨U, hU𝒰, hUV⟩
    exact inter_nonempty_of_subset_right_4_5 (hyp U hU𝒰) hUV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough that one neighborhood basis meets `A`. -/
theorem mem_closure_iff_exists_neighborhoodBasis_4_5
  (A : Set X) (x : X) :
    x ∈ closure_4_1 𝒪 A <->
      ∃ 𝒰 : Set (Set X), IsNeighborhoodBasis_2_5 𝒪 x 𝒰 ∧
        ∀ V ∈ 𝒰, (A ∩ V).Nonempty := by
  constructor
  · intro hx
    refine ⟨{V : Set X | IsNeighborhood_2_1 𝒪 x V},
      allNeighborhoods_isNeighborhoodBasis_2_6 x, ?_⟩
    intro V hV
    exact (mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x).mp hx V (mem_setOf.mp hV)
  · rintro ⟨𝒰, h𝒰, hA𝒰⟩
    refine (mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x).2 ?_
    intro V hV
    rcases h𝒰.hasRefinement V hV with ⟨U, hU𝒰, hUV⟩
    exact inter_nonempty_of_subset_right_4_5 (hA𝒰 U hU𝒰) hUV

/-!
Example 4.6 applies Proposition 4.5 to subsets of `ℝ`, showing that the
supremum and infimum of a nonempty bounded set lie in its closure, and belong
to the set itself when the set is closed.
-/

section RealPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.6: the supremum of a nonempty bounded-above subset of `ℝ` lies in its closure. -/
theorem sSup_mem_closure_4_6 {A : Set ℝ}
  (hA : A.Nonempty) (hA_bdd : BddAbove A) :
    sSup A ∈ closure_4_1 (@inducedTopology_1_17 ℝ inferInstance) A := by
  set 𝒪 : Set (Set ℝ) := inducedTopology_1_17 with 𝒪df
  have h𝒪 : IsTopology_1_1 ℝ 𝒪 := by
    rw [𝒪df]
    exact inducedTopology_isTopology_1_17
  set x := sSup A with xdf
  set 𝒰 : Set (Set ℝ) := {U | ∃ ε > 0, U = Ioo (x - ε) (x + ε)}
    with 𝒰df
  have h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰 := by
    rw [𝒪df, 𝒰df]
    exact real_openInterval_isNeighborhoodBasis_2_8 x

  apply mem_closure_iff_exists_neighborhoodBasis_4_5
    A x |>.mpr
  use 𝒰; constructor
  · exact h𝒰
  · intro V hV
    rcases hV with ⟨ε, εpos, Veq⟩
    have hxlt : x - ε < x := by linarith
    obtain ⟨a, haA, hax⟩ := exists_lt_of_lt_csSup hA hxlt
    have hxa : a ≤ x := le_csSup hA_bdd haA
    have haV : a ∈ V := by
      rw [Veq, Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
    exact ⟨a, haA, haV⟩

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.6: the infimum of a nonempty bounded-below subset of `ℝ` lies in its closure. -/
theorem sInf_mem_closure_4_6 {A : Set ℝ}
  (hA : A.Nonempty) (hA_bdd : BddBelow A) :
    sInf A ∈ closure_4_1 (@inducedTopology_1_17 ℝ inferInstance) A := by
  set 𝒪 : Set (Set ℝ) := inducedTopology_1_17 with 𝒪df
  have h𝒪 : IsTopology_1_1 ℝ 𝒪 := by
    rw [𝒪df]
    exact inducedTopology_isTopology_1_17
  set x := sInf A with xdf
  set 𝒰 : Set (Set ℝ) := {U | ∃ ε > 0, U = Ioo (x - ε) (x + ε)}
    with 𝒰df
  have h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰 := by
    rw [𝒪df, 𝒰df]
    exact real_openInterval_isNeighborhoodBasis_2_8 x

  apply mem_closure_iff_exists_neighborhoodBasis_4_5
    A x |>.mpr
  use 𝒰; constructor
  · exact h𝒰
  · intro V hV
    rcases hV with ⟨ε, εpos, Veq⟩
    have hxlt : x < x + ε := by linarith
    obtain ⟨a, haA, haxp⟩ := exists_lt_of_csInf_lt hA hxlt
    have hax : x ≤ a := csInf_le hA_bdd haA
    have haV : a ∈ V := by
      rw [Veq, Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
    exact ⟨a, haA, haV⟩

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.6: a nonempty bounded-above closed subset of `ℝ` contains its supremum. -/
theorem sSup_mem_of_isClosed_4_6 {A : Set ℝ}
  (hA_closed : IsClosed_1_2 (@inducedTopology_1_17 ℝ inferInstance) A)
    (hA : A.Nonempty) (hA_bdd : BddAbove A) :
      sSup A ∈ A := by
  set 𝒪 := @inducedTopology_1_17 ℝ _ with 𝒪df
  have h𝒪 : IsTopology_1_1 ℝ 𝒪 := by
    rw [𝒪df]
    exact inducedTopology_isTopology_1_17
  have : closure_4_1 inducedTopology_1_17 A = A
    := isClosed_iff_eq_closure_4_3 h𝒪 A
      |>.mp hA_closed
  nth_rw 1 [← this]
  exact sSup_mem_closure_4_6 hA hA_bdd

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.6: a nonempty bounded-below closed subset of `ℝ` contains its infimum. -/
theorem sInf_mem_of_isClosed_4_6 {A : Set ℝ}
  (hA_closed : IsClosed_1_2 (@inducedTopology_1_17 ℝ inferInstance) A)
    (hA : A.Nonempty) (hA_bdd : BddBelow A) :
      sInf A ∈ A := by
  set 𝒪 := @inducedTopology_1_17 ℝ _ with 𝒪df
  have h𝒪 : IsTopology_1_1 ℝ 𝒪 := by
    rw [𝒪df]
    exact inducedTopology_isTopology_1_17
  have : closure_4_1 inducedTopology_1_17 A = A
    := isClosed_iff_eq_closure_4_3 h𝒪 A
      |>.mp hA_closed
  nth_rw 1 [← this]
  exact sInf_mem_closure_4_6 hA hA_bdd

end RealPart

/-!
Proposition 4.7 4.8 and Example 4.9 specialize closure to distance spaces.
We record only the statement skeletons here.
-/

section MetricPart

variable [DistanceSpace_1_12 X]

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.7: in a distance space,
  closure points are exactly limits of sequences from the set. -/
theorem mem_closure_iff_exists_tendstoSeq_4_7 (A : Set X) (x : X) :
  x ∈ closure_4_1 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) A
    <-> ∃ xₙ : Sequence_2_16 X, (∀ n : ℕ, xₙ n ∈ A) ∧
      TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ x
        := open Classical in by
  set 𝒪 := @inducedTopology_1_17 X _ with 𝒪df
  have h𝒪 : IsTopology_1_1 X 𝒪
    := inducedTopology_isTopology_1_17
  constructor
  <;> intro hyp
  · have h𝒰
      := distance_invPNatBall_isNeighborhoodBasis_2_8 x
    set 𝒰 := {U | ∃ n : ℕ+, U = openBall_1_14 x (1 / ↑↑n) }
      with 𝒰df
    have := mem_closure_iff_neighborhoodBasis_4_5
      h𝒪 A x 𝒰 h𝒰 |>.mp hyp
    have : ∀ n : ℕ+, (A ∩ openBall_1_14  x (1 / ↑↑n)).Nonempty := by
      intro n
      simp only [
        𝒰df, mem_setOf_eq,
        forall_exists_index,
        forall_eq_apply_imp_iff
      ] at this
      exact this n
    have : ∀ n : ℕ, (A ∩ openBall_1_14  x (1 / (↑n + 1))).Nonempty := by
      intro n
      have h := this ⟨n + 1, Nat.succ_pos n⟩
      simpa [PNat.mk_coe, Nat.cast_add, Nat.cast_one] using h
    choose f' hf' using this
    set f : Sequence_2_16 X := id f' with fdf
    use f; constructor
    · intro n
      specialize hf' n
      simp only [fdf, id_eq]
      exact mem_of_mem_inter_left hf'
    · intro V hV
      have := h𝒰.hasRefinement V hV
      rcases this with ⟨U, Uin𝒰, UsubV⟩
      simp only [𝒰df, mem_setOf_eq] at Uin𝒰
      rcases Uin𝒰 with ⟨N₀, Ueq₀⟩
      set N : ℕ := N₀ - 1 with Ndf
      have : N + 1 = N₀ := by exact PNat.natPred_add_one N₀
      rw [← this] at Ueq₀
      use N; intro n hn
      specialize hf' n
      simp only [fdf, id_eq]
      have hmem : f' n ∈ openBall_1_14 x (1 / (↑n + 1)) := mem_of_mem_inter_right hf'
      have hU : f' n ∈ U := by
        rw [openBall_1_14, mem_setOf_eq] at hmem
        have hball : f' n ∈ openBall_1_14 x (1 / ↑(N + 1)) := by
          rw [openBall_1_14, mem_setOf_eq]
          refine lt_of_lt_of_le hmem ?_
          have hle_nat : N + 1 ≤ n + 1 := Nat.succ_le_succ hn
          have hle : (n : ℝ) + 1 ≥ (N : ℝ) + 1 := by
            exact_mod_cast hle_nat
          have hposN : 0 < (N : ℝ) + 1 := by positivity
          have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            exact one_div_le_one_div_of_le hposN hle
          simpa using hrecip
        simpa [Ueq₀] using hball
      exact UsubV hU
  · rcases hyp with ⟨xₙ, hxₙ, xₙcvg⟩
    apply mem_closure_iff_neighborhood_4_5' A x
      |>.mpr
    intro V hV; specialize xₙcvg V hV
    rcases xₙcvg with ⟨N, hN⟩
    specialize hN N (by linarith)
    specialize hxₙ N
    use xₙ N
    exact mem_inter hxₙ hN

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.8: in a distance space,
  closed sets are exactly those closed under limits of sequences. -/
theorem isClosed_iff_tendstoSeq_mem_4_8 (A : Set X) :
  IsClosed_1_2 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) A
    <-> ∀ xₙ : Sequence_2_16 X, (∀ n : ℕ, xₙ n ∈ A)
      -> ∀ x : X, TendstoSeq_2_16 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) xₙ x
        -> x ∈ A := by
  have h𝒪 : IsTopology_1_1
    X (inducedTopology_1_17 (X := X)) := by
      exact inducedTopology_isTopology_1_17
  constructor
  <;> intro hyp
  · intro xₙ hxₙ x xₙcvg
    have : A = closure_4_1
      (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
        A := by
      exact (isClosed_iff_eq_closure_4_3 h𝒪 A).mp hyp |>.symm
    rw [this]
    exact mem_closure_iff_exists_tendstoSeq_4_7 A x
      |>.mpr ⟨xₙ, hxₙ, xₙcvg⟩
  · apply isClosed_of_closure_subset_4_3 h𝒪 A
    intro x hx
    rcases mem_closure_iff_exists_tendstoSeq_4_7 A x
      |>.mp hx with ⟨xₙ, hxₙ, xₙcvg⟩
    exact hyp xₙ hxₙ x xₙcvg

end MetricPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (1): in a discrete space, every set equals its closure. -/
theorem closure_eq_self_discrete_4_9_1
    (𝒪df : 𝒪 = discreteTopology_1_6 X) (A : Set X) :
    closure_4_1 𝒪 A = A := by
  have h𝒪 : IsTopology_1_1 X 𝒪
    := 𝒪df ▸ discreteTopology_isTopology_1_6 X
  have : IsClosed_1_2 𝒪 A := by
    simp only [
      IsClosed_1_2, 𝒪df,
      discreteTopology_1_6,
      mem_univ
    ]
  exact (isClosed_iff_eq_closure_4_3 h𝒪 A).mp this

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (2): in the indiscrete space, every nonempty set is dense. -/
theorem closure_eq_univ_of_nonempty_indiscrete_4_9_2
  (𝒪df : 𝒪 = indiscreteTopology_1_7 X) {A : Set X} (hA : A.Nonempty) :
    closure_4_1 𝒪 A = univ := by
  have h𝒪 : IsTopology_1_1 X 𝒪
    := 𝒪df ▸ indiscreteTopology_isTopology_1_7 X
  /- There is only two close set in 𝒪 : ∅ and univ
    which is clearly that
      closure_4_1 will be one of them. -/
  ext x
  constructor
  · intro _
    simp
  · intro _
    simp only [closure_4_1, ClosedSupersets_4_1, mem_sInter, mem_setOf_eq]
    intro F hF
    rcases hF with ⟨hFclosed, hAF⟩
    rw [IsClosed_1_2, 𝒪df, indiscreteTopology_1_7,
      mem_insert_iff, mem_singleton_iff] at hFclosed
    rcases hFclosed with hFcempty | hFcuniv
    · have hFuniv : F = univ := by
        ext y
        constructor
        · intro _
          simp
        · intro hy
          by_cases hyF : y ∈ F
          · exact hyF
          · exfalso
            have hyc : y ∈ Fᶜ := by simpa [Set.mem_compl_iff] using hyF
            simp [hFcempty] at hyc
      simp [hFuniv]
    · exfalso
      rcases hA with ⟨a, haA⟩
      have haF : a ∈ F := hAF haA
      have hFempty : F = ∅ := by
        ext y
        constructor
        · intro hy
          have hyc : y ∈ Fᶜ := by simpa [hFcuniv]
            using (show y ∈ (univ : Set X) from by simp)
          have hy_not : y ∉ Fᶜ := by simpa [Set.mem_compl_iff] using hy
          exact hy_not hyc
        · intro hy
          exact False.elim (by simpa using hy)
      simp [hFempty] at haF

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (2): in the indiscrete space, the empty set has empty closure. -/
theorem closure_empty_indiscrete_4_9_2
  (h𝒪 : 𝒪 = indiscreteTopology_1_7 X) :
    closure_4_1 𝒪 (∅ : Set X) = ∅ := by
  /- Nothing interesting here. -/
  have hTop : IsTopology_1_1 X 𝒪 :=
    h𝒪 ▸ indiscreteTopology_isTopology_1_7 X
  have hEmptyClosed : IsClosed_1_2 𝒪 (∅ : Set X) := by
    simp [IsClosed_1_2, h𝒪, indiscreteTopology_1_7]
  exact (isClosed_iff_eq_closure_4_3 hTop (∅ : Set X)).mp hEmptyClosed

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (3): in the finite-complement topology, every finite set equals its closure. -/
theorem closure_eq_self_finiteComplement_finite_4_9_3
  (𝒪df : 𝒪 = finiteComplementTopology_1_8 X) {A : Set X} (hA : A.Finite) :
    closure_4_1 𝒪 A = A := by
  have h𝒪 : IsTopology_1_1 X 𝒪 :=
    𝒪df ▸ finiteComplementTopology_isTopology_1_8 X
  have hA_closed : IsClosed_1_2 𝒪 A := by
    rw [IsClosed_1_2, 𝒪df, finiteComplementTopology_1_8]
    simp [hA]
  exact (isClosed_iff_eq_closure_4_3 h𝒪 A).mp hA_closed

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (3): in the finite-complement topology on an infinite space,
every infinite set is dense. -/
theorem closure_eq_univ_finiteComplement_infinite_4_9_3
  [Infinite X] (𝒪df : 𝒪 = finiteComplementTopology_1_8 X)
  {A : Set X} (hA : A.Infinite) :
    closure_4_1 𝒪 A = univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    simp only [closure_4_1, ClosedSupersets_4_1, mem_sInter, mem_setOf_eq]
    intro F hF
    rcases hF with ⟨hFclosed, hAF⟩
    have hF' : F = univ ∨ F.Finite := by
      rw [IsClosed_1_2, 𝒪df, finiteComplementTopology_1_8] at hFclosed
      simpa using hFclosed
    rcases hF' with hFuniv | hFfin
    · simpa only [hFuniv]
    · exfalso
      exact hA.not_finite (hFfin.subset hAF)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (4): in `ℝ`, the closure of `(-1, 1)` is `[-1, 1]`. -/
theorem closure_Ioo_neg_one_one_4_9_4 :
  closure_4_1 (@inducedTopology_1_17 ℝ inferInstance) (Set.Ioo (-1 : ℝ) 1)
    = Set.Icc (-1 : ℝ) 1 := by
  set 𝒪 := @inducedTopology_1_17 ℝ inferInstance
  have h𝒪 : IsTopology_1_1 ℝ 𝒪 := by
    exact inducedTopology_isTopology_1_17
  set A := Ioo (-1 : ℝ) 1
  set A' := closure_4_1 inducedTopology_1_17 A
  set B := Icc (-1 : ℝ) 1
  
  have c1 : ∀ x > 1, x ∉ A' := by
    intro x hx
    set U := {x | x > (1 : ℝ)}
    have Uop : U ∈ 𝒪 := by
      simp [𝒪]
      intro y hy
      refine ⟨y - 1, sub_pos.mpr hy, ?_⟩
      intro z hz
      simp [U, openBall_1_14, Real.dist_eq] at hz ⊢
      have hz' := abs_lt.mp hz
      linarith
    have hxU : IsNeighborhood_2_1 𝒪 x U
      := neighborhood_of_open_mem Uop hx
    have hAU : A ∩ U = ∅ := by
      ext y
      constructor <;> intro hy
      · rcases hy with ⟨hyA, hyU⟩
        simp [A, U] at hyA hyU
        exact False.elim (by linarith)
      · exact False.elim hy
    intro hyp
    have := mem_closure_iff_neighborhood_4_5' A x
      |>.mp hyp U hxU
    rw [hAU] at this
    rcases this with ⟨y, hy⟩
    exact hy
  
  have c2 : ∀ x < -1, x ∉ A' := by
    /- simular with c1 -/
    intro x hx
    set U := {x | x < (-1 : ℝ)}
    have Uop : U ∈ 𝒪 := by
      simp [𝒪]
      intro y hy
      refine ⟨-1 - y, sub_pos.mpr hy, ?_⟩
      intro z hz
      simp [U, openBall_1_14, Real.dist_eq] at hz ⊢
      have hz' := abs_lt.mp hz
      linarith
    have hxU : IsNeighborhood_2_1 𝒪 x U
      := neighborhood_of_open_mem Uop hx
    have hAU : A ∩ U = ∅ := by
      ext y
      constructor <;> intro hy
      · rcases hy with ⟨hyA, hyU⟩
        simp [A, U] at hyA hyU
        exact False.elim (by linarith)
      · exact False.elim hy
    intro hyp
    have := mem_closure_iff_neighborhood_4_5' A x
      |>.mp hyp U hxU
    rw [hAU] at this
    rcases this with ⟨y, hy⟩
    exact hy
  
  have c3 : 1 ∈ A' := by
    set xₙ : Sequence_2_16 ℝ := λ n ↦ 1 - 1 / (↑n + 1)
    have xₙcvg: TendstoSeq_2_16 𝒪 xₙ 1 := by
      refine (tendstoSeq_metric_2_19 xₙ 1).topo_iff_eps.mpr ?_
      intro ε εpos
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      use N
      intro n hn
      have hN' : (1 / ε) < (n : ℝ) + 1 := by
        have hle : (N : ℝ) ≤ (n : ℝ) + 1 := by
          have hle' : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        linarith
      have hmul : 1 < ε * ((n : ℝ) + 1) := by
        have hm := mul_lt_mul_of_pos_right hN' εpos
        simpa [one_div, εpos.ne', mul_comm, mul_left_comm, mul_assoc] using hm
      have hdist : 1 / ((n : ℝ) + 1) < ε := by
        have hpos : 0 < (n : ℝ) + 1 := by positivity
        field_simp [hpos.ne', εpos.ne'] at hN' ⊢
        linarith
      have hEq : DistanceSpace_1_12.dist (xₙ n) 1 = 1 / ((n : ℝ) + 1) := by
        change dist (xₙ n) 1 = 1 / ((n : ℝ) + 1)
        rw [Real.dist_eq]
        have hnonpos : xₙ n - 1 ≤ 0 := by
          dsimp [xₙ]
          have hnonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          linarith
        rw [abs_of_nonpos hnonpos]
        dsimp [xₙ]
        ring
      rw [hEq]
      exact hdist
    apply mem_closure_iff_exists_tendstoSeq_4_7 A 1 |>.mpr
    use xₙ; constructor
    · intro n
      simp [A]
      constructor
      · have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
          have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            nlinarith [show (0 : ℝ) ≤ n by positivity]
          have h0 : (0 : ℝ) < 1 := by norm_num
          simpa using one_div_le_one_div_of_le h0 h1
        dsimp [xₙ]
        linarith
      · dsimp [xₙ]
        have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    · exact xₙcvg
  
  have c4 : -1 ∈ A' := by
    /- simular with c3 -/
    set xₙ : Sequence_2_16 ℝ := λ n ↦ -1 + 1 / (↑n + 1)
    have xₙcvg: TendstoSeq_2_16 𝒪 xₙ (-1) := by
      refine (tendstoSeq_metric_2_19 xₙ (-1)).topo_iff_eps.mpr ?_
      intro ε εpos
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      use N
      intro n hn
      have hN' : (1 / ε) < (n : ℝ) + 1 := by
        have hle : (N : ℝ) ≤ (n : ℝ) + 1 := by
          have hle' : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        linarith
      have hmul : 1 < ε * ((n : ℝ) + 1) := by
        have hm := mul_lt_mul_of_pos_right hN' εpos
        simpa [one_div, εpos.ne', mul_comm, mul_left_comm, mul_assoc] using hm
      have hdist : 1 / ((n : ℝ) + 1) < ε := by
        have hpos : 0 < (n : ℝ) + 1 := by positivity
        field_simp [hpos.ne', εpos.ne'] at hN' ⊢
        linarith
      have hEq : DistanceSpace_1_12.dist (xₙ n) (-1) = 1 / ((n : ℝ) + 1) := by
        change dist (xₙ n) (-1) = 1 / ((n : ℝ) + 1)
        rw [Real.dist_eq]
        have hnonneg : 0 ≤ xₙ n - (-1) := by
          have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          simpa [xₙ]
        rw [abs_of_nonneg hnonneg]
        dsimp [xₙ]
        ring
      rw [hEq]
      exact hdist
    apply mem_closure_iff_exists_tendstoSeq_4_7 A (-1) |>.mpr
    use xₙ; constructor
    · intro n
      simp [A]
      constructor
      · dsimp [xₙ]
        have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
          have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            nlinarith [show (0 : ℝ) ≤ n by positivity]
          have h0 : (0 : ℝ) < 1 := by norm_num
          simpa using one_div_le_one_div_of_le h0 h1
        dsimp [xₙ]
        linarith
    · exact xₙcvg
  
  ext x
  constructor
  · intro hx
    simp [B]
    constructor
    · by_contra hxlt
      exact (c2 x (lt_of_not_ge hxlt)) hx
    · by_contra hxgt
      exact (c1 x (lt_of_not_ge hxgt)) hx
  · intro hx
    simp [B] at hx
    rcases hx with ⟨hxL, hxR⟩
    by_cases hx1 : x = 1
    · simpa [A', hx1] using c3
    · by_cases hxneg1 : x = -1
      · simpa [A', hxneg1] using c4
      · have hxA : x ∈ A := by
          simp [A]
          constructor
          · have hxLt : -1 < x := lt_of_le_of_ne hxL (Ne.symm hxneg1)
            exact hxLt
          · have hxGt : x < 1 := lt_of_le_of_ne hxR hx1
            exact hxGt
        simpa [A'] using
          (subset_closure_4_1
            (𝒪 := inducedTopology_1_17) A hxA)

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (5): in Euclidean space, the rational-coordinate points are dense. -/
theorem closure_eq_univ_rationalPoints_euclidean_4_9_5 (n : ℕ) :
  letI : DistanceSpace_1_12 (E n) :=
    euclideanDistanceSpace_1_12 n
  closure_4_1 (@inducedTopology_1_17 (E n) ‹_›)
    {x : E n | ∀ i : Fin n, ∃ q : ℚ, x i = (q : ℝ)}
      = univ := by
  set 𝒪 := @inducedTopology_1_17 (E n) _
  have h𝒪 : IsTopology_1_1 (E n) 𝒪 := by
    rw [show 𝒪 = @inducedTopology_1_17 (E n) _ by rfl]
    exact inducedTopology_isTopology_1_17
  set A := {x : E n | ∀ i : Fin n, ∃ q : ℚ, x i = (q : ℝ)}
  ext x
  constructor<;> intro hyp
  · exact mem_univ x
  · have h𝒰 := distance_openBall_isNeighborhoodBasis_2_8 x
    set 𝒰 := {U | ∃ r > 0, U = openBall_1_14 x r}
    apply mem_closure_iff_neighborhoodBasis_4_5 h𝒪 A x 𝒰 h𝒰 |>.mpr
    intro B hB
    dsimp [𝒰] at hB
    rcases hB with ⟨ε, εpos, hB⟩
    have hsqrtpos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      apply Real.sqrt_pos.2
      positivity
    have : ∀ i : Fin n, ∃ yₙ : ℚ,
      dist (x i) yₙ < ε / Real.sqrt ((n : ℝ) + 1) := by
      intro i
      obtain ⟨q, hqL, hqR⟩ := exists_rat_btwn (show
        x i - ε / Real.sqrt ((n : ℝ) + 1) < x i + ε / Real.sqrt ((n : ℝ) + 1) by
          have : 0 < ε / Real.sqrt ((n : ℝ) + 1) := by positivity
          linarith)
      refine ⟨q, ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    fin_choose f hf using this
    set y : E n := by
      exact WithLp.toLp 2 (λ i ↦ (f i : ℝ))
    have hyA : y ∈ A := by
      dsimp [A]
      intro i
      refine ⟨f i, ?_⟩
      simp [y]
    have hsq_le : ∀ k ∈ Finset.univ,
        ((y - x) k) ^ 2 ≤ (ε / Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
      intro k hk
      have hk' : dist (x k) (f k) < ε / Real.sqrt ((n : ℝ) + 1) := hf k
      rw [Real.dist_eq] at hk'
      have hcoord : |(y - x) k| < ε / Real.sqrt ((n : ℝ) + 1) := by
        simpa [y, abs_sub_comm] using hk'
      nlinarith [abs_lt.mp hcoord |>.1, abs_lt.mp hcoord |>.2]
    have : dist y x < ε := by
      have hdistsq : dist y x ^ 2 < ε ^ 2 := by
        calc
          dist y x ^ 2 = ∑ k : Fin n, ((y - x) k) ^ 2 := by
            rw [dist_eq_norm]
            simpa using EuclideanSpace.real_norm_sq_eq (y - x)
          _ ≤ (n : ℝ) * (ε / Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
            simpa using
              Finset.sum_le_card_nsmul
                Finset.univ
                (fun k : Fin n ↦ ((y - x) k) ^ 2)
                ((ε / Real.sqrt ((n : ℝ) + 1)) ^ 2)
                hsq_le
          _ < ((n : ℝ) + 1) * (ε / Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
            have hεsq_pos : 0 < (ε / Real.sqrt ((n : ℝ) + 1)) ^ 2 := by positivity
            nlinarith
          _ = ε ^ 2 := by
            field_simp [hsqrtpos.ne']
            rw [Real.sq_sqrt]
            positivity
      have hdist_nonneg : 0 ≤ dist y x := by
        exact DistanceSpace_1_12.nonneg y x
      nlinarith [hdist_nonneg, εpos, hdistsq]
    have hyB : y ∈ B := by
      simpa [hB, openBall_1_14, dist_comm] using this
    exact ⟨y, mem_inter hyA hyB⟩

/-!
Definition 4.10 introduces dense subsets, and Definition 4.13 introduces
separability.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.10: `A` is dense if its closure is all of `X`. -/
def IsDense_4_10 (𝒪 : Set (Set X)) (A : Set X) : Prop :=
  closure_4_1 𝒪 A = univ

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.11: `A` is dense iff every nonempty open set meets `A`. -/
theorem isDense_iff_open_4_11 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
  IsDense_4_10 𝒪 A
    <-> ∀ U : Set X, U ∈ 𝒪 → U.Nonempty → (A ∩ U).Nonempty := by
  constructor
  · intro hA U hU hUne
    rcases hUne with ⟨x, hxU⟩
    have hxCl : x ∈ closure_4_1 𝒪 A := by
      rw [hA]
      simp
    exact (mem_closure_iff_openNeighborhood_4_5 h𝒪 A x).mp hxCl U
      ⟨neighborhood_of_open_mem hU hxU, hU⟩
  · intro hU
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact (mem_closure_iff_openNeighborhood_4_5 h𝒪 A x).mpr <| by
      intro V hV
      exact hU V hV.2 ⟨x, (openNeighborhood_iff_2_2 h𝒪 x V).mp hV |>.2⟩

/-!
Example 4.12 and Propositions 4.14–4.15 discuss the relation between density,
separability, and countability axioms.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.12: the rational-coordinate points are dense in Euclidean space. -/
theorem rationalPoints_dense_euclidean_4_12 (n : ℕ) :
    letI : DistanceSpace_1_12 (E n) :=
      euclideanDistanceSpace_1_12 n
    IsDense_4_10 (@inducedTopology_1_17 (E n) ‹_›)
      {x : E n | ∀ i : Fin n, ∃ q : ℚ, x i = (q : ℝ)} := by
  simpa [IsDense_4_10] using closure_eq_univ_rationalPoints_euclidean_4_9_5 n

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.13: a topology is separable if it has a countable dense subset. -/
def IsSeparable_4_13 (𝒪 : Set (Set X)) : Prop :=
  ∃ A : Set X, A.Countable ∧ IsDense_4_10 𝒪 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.14: every second-countable space is separable. -/
theorem secondCountable_implies_separable_4_14
  {X : Type u} {𝒪 : Set (Set X)} :
    SecondCountable_3_6 𝒪 -> IsSeparable_4_13 𝒪
      := open Classical in by
  intro hyp
  rcases hyp with ⟨ℬ, ⟨ℬsub𝒪, hℬ⟩ , ℬ_ctb⟩
  set ℬ' : Set (Set X) := { B ∈ ℬ | B.Nonempty }
  have : ∀ B ∈ ℬ', ∃ x, x ∈ B := by
    intro B hB
    exact hB.2
  choose f hf using this
  set A := {x | ∃ B, ∃ (h : B ∈ ℬ'), x = f B h}
  use A; constructor
  · have hAsub : A ⊆ Set.range fun p : {B // B ∈ ℬ'} => f p.1 p.2 := by
      intro x hx
      rcases hx with ⟨B, hB, rfl⟩
      exact ⟨⟨B, hB⟩, rfl⟩
    have hℬ'_ctb : ℬ'.Countable := ℬ_ctb.mono (by
      intro B hB
      exact hB.1)
    haveI : Countable {B // B ∈ ℬ'} := hℬ'_ctb.to_subtype
    exact Set.Countable.mono hAsub (Set.countable_range fun p : {B // B ∈ ℬ'} => f p.1 p.2)
  · ext x
    constructor
    · intro _
      exact mem_univ x
    · intro hyp
      simp only [closure_4_1,
        ClosedSupersets_4_1,
        mem_sInter, mem_setOf_eq, and_imp]
      intro F Fcl AsubF
      by_contra ct
      have hxFc : x ∈ Fᶜ := (mem_compl_iff F x).mpr ct
      have opFc : Fᶜ ∈ 𝒪 := open_of_closed_compl Fcl
      have : ∃ B ∈ ℬ', x ∈ B ∧ B ⊆ Fᶜ := by
        rcases hℬ (Fᶜ) opFc x hxFc with ⟨B, hBℬ, hxB, hBFc⟩
        exact ⟨B, ⟨hBℬ, ⟨x, hxB⟩⟩, hxB, hBFc⟩
      rcases this with ⟨B, Binℬ', xinB, BsubFc⟩
      specialize hf B Binℬ'
      have c2 : f B Binℬ' ∈ A := by
        exact ⟨B, Binℬ', rfl⟩
      have hFmem : f B Binℬ' ∈ F := AsubF c2
      have hFcmem : f B Binℬ' ∈ Fᶜ := BsubFc hf
      exact hFcmem hFmem

section MetricCountabilityPart

variable [DistanceSpace_1_12 X]

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.15: every separable distance space is second countable. -/
theorem separable_metric_implies_secondCountable_4_15 :
    IsSeparable_4_13 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›)
      -> Basis.SecondCountable_3_6 (@inducedTopology_1_17 X ‹DistanceSpace_1_12 X›) := by
  sorry

end MetricCountabilityPart

section CountabilityExamplesPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: every finite-complement space is separable. -/
theorem finiteComplement_separable_4_16 (X : Type u) :
    IsSeparable_4_13 (finiteComplementTopology_1_8 X) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: an uncountable finite-complement space is not first countable. -/
theorem uncountable_finiteComplement_not_firstCountable_4_16
    (X : Type u) [Uncountable X] :
    ¬ FirstCountable_2_12 (finiteComplementTopology_1_8 X) := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: an uncountable finite-complement space is not second countable. -/
theorem uncountable_finiteComplement_not_secondCountable_4_16
    (X : Type u) [Uncountable X] :
    ¬ Basis.SecondCountable_3_6 (finiteComplementTopology_1_8 X) := by
  sorry

end CountabilityExamplesPart

/-!
Proposition 4.17 packages the standard closure-operator laws.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.17: an abstract closure operator on `P(X)`. -/
structure IsClosureOperator_4_17 (Cl : Set X -> Set X) : Prop where
  C1_empty : Cl ∅ = ∅
  C2_extensive : ∀ A : Set X, A ⊆ Cl A
  C3_union : ∀ A B : Set X, Cl (A ∪ B) = Cl A ∪ Cl B
  C4_idem : ∀ A : Set X, Cl (Cl A) = Cl A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure of the empty set. -/
theorem closure_empty_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) :
    closure_4_1 𝒪 (∅ : Set X) = ∅ := by
  unfold closure_4_1
  ext x
  constructor
  <;> intro hyp
  · have : ∀ F ∈ ClosedSupersets_4_1 𝒪 ∅, x ∈ F
      := λ F a ↦ mem_of_subset_of_mem
        (λ ⦃_⦄ ↦ id) (hyp F a)
    specialize this ∅
    apply this
    simp only [
      ClosedSupersets_4_1,
      empty_subset,
      and_true, mem_setOf_eq
    ]
    exact closedSet_properties_1_3.mp h𝒪
      |>.C1_empty
  · intro F hF
    exact not_notMem.mp λ _ ↦ hyp

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure is extensive. -/
theorem closure_extensive_4_17 (A : Set X) :
    A ⊆ closure_4_1 𝒪 A :=
  subset_closure_4_1 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure preserves finite unions. -/
theorem closure_union_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) (A B : Set X) :
    closure_4_1 𝒪 (A ∪ B) = closure_4_1 𝒪 A ∪ closure_4_1 𝒪 B := by
  refine Subset.antisymm_iff.mpr ?_
  constructor
  · have c1 : A ⊆ closure_4_1 𝒪 A := closure_extensive_4_17 A
    have c2 : B ⊆ closure_4_1 𝒪 B := closure_extensive_4_17 B
    have c3 : A ∪ B ⊆ (closure_4_1 𝒪 A) ∪ (closure_4_1 𝒪 B)
      := union_subset_union c1 c2
    have hAB : IsClosed_1_2 𝒪
      ((closure_4_1 𝒪 A) ∪ (closure_4_1 𝒪 B))
        := by
      apply closedSet_properties_1_3.mp h𝒪 |>.C2_union
      · simp only [mem_setOf_eq]
        exact closure_isClosed_4_1 h𝒪 A
      · simp only [mem_setOf_eq]
        exact closure_isClosed_4_1 h𝒪 B
    exact closure_minimal_4_2 (A ∪ B)
      (closure_4_1 𝒪 A ∪ closure_4_1 𝒪 B) hAB c3
  · have c1 : closure_4_1 𝒪 A ⊆ closure_4_1 𝒪 (A ∪ B) := by
      have : A ⊆ A ∪ B := subset_union_left
      exact closure_mono_4_4 this
    have c2 : closure_4_1 𝒪 B ⊆ closure_4_1 𝒪 (A ∪ B) := by
      have : B ⊆ A ∪ B := subset_union_right
      exact closure_mono_4_4 this
    exact union_subset c1 c2

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure is idempotent. -/
theorem closure_idem_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    closure_4_1 𝒪 (closure_4_1 𝒪 A) = closure_4_1 𝒪 A := by
  have : IsClosed_1_2 𝒪 (closure_4_1 𝒪 A)
    := closure_isClosed_4_1 h𝒪 A
  exact (isClosed_iff_eq_closure_4_3 h𝒪
    (closure_4_1 𝒪 A)).mp this

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: the topological closure map satisfies the closure-operator axioms. -/
theorem closure_isClosureOperator_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) :
    IsClosureOperator_4_17 (closure_4_1 𝒪) := by
  sorry

/-!
Proposition 4.18 reconstructs a topology from an abstract closure operator.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.18: the topology determined by a closure operator. -/
def topologyFromClosureOperator_4_18 (Cl : Set X -> Set X) : Set (Set X) :=
  {U : Set X | Cl Uᶜ = Uᶜ}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.18: closure-operator axioms determine a unique topology. -/
structure ClosureOperatorTopologyData_4_18 (Cl : Set X -> Set X) : Prop where
  isTopology : IsClosureOperator_4_17 Cl -> IsTopology_1_1 X (topologyFromClosureOperator_4_18 Cl)
  closure_eq :
    IsClosureOperator_4_17 Cl ->
      ∀ A : Set X, closure_4_1 (topologyFromClosureOperator_4_18 Cl) A = Cl A
  unique :
    IsClosureOperator_4_17 Cl ->
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 ->
        (∀ A : Set X, closure_4_1 𝒪 A = Cl A) ->
          𝒪 = topologyFromClosureOperator_4_18 Cl

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.18: a closure operator determines a unique topology. -/
theorem topology_from_closureOperator_4_18 (Cl : Set X -> Set X)
    (hCl : IsClosureOperator_4_17 Cl) :
    ClosureOperatorTopologyData_4_18 (X := X) Cl := by
  sorry

/-!
Definition 4.19 introduces interior as the union of all open subsets.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.19: the family of open subsets of `A`. -/
def OpenSubsets_4_19 (𝒪 : Set (Set X)) (A : Set X) : Set (Set X) :=
  {U : Set X | U ∈ 𝒪 ∧ U ⊆ A}

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.19: the interior of `A` is the union of all open subsets of `A`. -/
def interior_4_19 (𝒪 : Set (Set X)) (A : Set X) : Set X :=
  ⋃₀ OpenSubsets_4_19 𝒪 A

/-- Interior is open. -/
theorem interior_isOpen_4_19 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    interior_4_19 𝒪 A ∈ 𝒪 := by
  sorry

/-- Interior is contained in the original set. -/
theorem interior_subset_4_19 (A : Set X) :
    interior_4_19 𝒪 A ⊆ A := by
  intro x hx
  rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
  exact hU.2 hxU

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.20: every open subset of `A` lies in `interior A`. -/
theorem interior_maximal_4_20 (A U : Set X)
    (hUopen : U ∈ 𝒪) (hUA : U ⊆ A) :
    U ⊆ interior_4_19 𝒪 A := by
  sorry

/-- 𝒩ℴ𝓉ℯ 4.21: a set is open iff it equals its interior. -/
theorem isOpen_iff_eq_interior_4_21 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    A ∈ 𝒪 ↔ interior_4_19 𝒪 A = A := by
  sorry

/-- 𝒩ℴ𝓉ℯ 4.21: equivalently, a set is open iff it is contained in its interior. -/
theorem isOpen_iff_subset_interior_4_21 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    A ∈ 𝒪 ↔ A ⊆ interior_4_19 𝒪 A := by
  rw [isOpen_iff_eq_interior_4_21 h𝒪 A]
  constructor
  · intro hEq
    rw [hEq]
  · intro hSub
    exact Subset.antisymm (interior_subset_4_19 A) hSub

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: the complement of the interior is the closure of the complement. -/
theorem compl_interior_eq_closure_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    (interior_4_19 𝒪 A)ᶜ = closure_4_1 𝒪 Aᶜ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: dually, closure is the complement of the interior of the complement. -/
theorem closure_eq_compl_interior_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    closure_4_1 𝒪 A = (interior_4_19 𝒪 Aᶜ)ᶜ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: equivalently, the interior is the complement of the closure of the complement. -/
theorem interior_eq_compl_closure_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    interior_4_19 𝒪 A = (closure_4_1 𝒪 Aᶜ)ᶜ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.23: interior is monotone. -/
theorem interior_mono_4_23 {A B : Set X} (hAB : A ⊆ B) :
    interior_4_19 𝒪 A ⊆ interior_4_19 𝒪 B := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: interior points are exactly those admitting a neighborhood inside `A`. -/
theorem mem_interior_iff_neighborhood_4_24 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) :
    x ∈ interior_4_19 𝒪 A ↔ ∃ V : Set X, IsNeighborhood_2_1 𝒪 x V ∧ V ⊆ A := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: equivalently, one may use an open neighborhood contained in `A`. -/
theorem mem_interior_iff_openNeighborhood_4_24 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) :
    x ∈ interior_4_19 𝒪 A ↔ ∃ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V ∧ V ⊆ A := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: equivalently, `A` itself is a neighborhood of `x`. -/
theorem mem_interior_iff_isNeighborhood_4_24 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) :
    x ∈ interior_4_19 𝒪 A ↔ IsNeighborhood_2_1 𝒪 x A := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior of the whole space. -/
theorem interior_univ_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) :
    interior_4_19 𝒪 (univ : Set X) = univ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior is contractive. -/
theorem interior_contractive_4_25 (A : Set X) :
    interior_4_19 𝒪 A ⊆ A :=
  interior_subset_4_19 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior preserves finite intersections. -/
theorem interior_inter_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) (A B : Set X) :
    interior_4_19 𝒪 (A ∩ B) = interior_4_19 𝒪 A ∩ interior_4_19 𝒪 B := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior is idempotent. -/
theorem interior_idem_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    interior_4_19 𝒪 (interior_4_19 𝒪 A) = interior_4_19 𝒪 A := by
  sorry

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.25: an abstract interior operator on `P(X)`. -/
structure IsInteriorOperator_4_25 (Int : Set X -> Set X) : Prop where
  I1_univ : Int univ = univ
  I2_contractive : ∀ A : Set X, Int A ⊆ A
  I3_inter : ∀ A B : Set X, Int (A ∩ B) = Int A ∩ Int B
  I4_idem : ∀ A : Set X, Int (Int A) = Int A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: the topological interior map satisfies the interior-operator axioms. -/
theorem interior_isInteriorOperator_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) :
    IsInteriorOperator_4_25 (interior_4_19 𝒪) := by
  sorry

/-!
Proposition 4.26 reconstructs a topology from an abstract interior operator.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.26: the topology determined by an interior operator. -/
def topologyFromInteriorOperator_4_26 (Int : Set X -> Set X) : Set (Set X) :=
  {U : Set X | Int U = U}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.26: interior-operator axioms determine a unique topology. -/
structure InteriorOperatorTopologyData_4_26 (Int : Set X -> Set X) : Prop where
  isTopology : IsInteriorOperator_4_25 Int -> IsTopology_1_1 X (topologyFromInteriorOperator_4_26 Int)
  interior_eq :
    IsInteriorOperator_4_25 Int ->
      ∀ A : Set X, interior_4_19 (topologyFromInteriorOperator_4_26 Int) A = Int A
  unique :
    IsInteriorOperator_4_25 Int ->
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 ->
        (∀ A : Set X, interior_4_19 𝒪 A = Int A) ->
          𝒪 = topologyFromInteriorOperator_4_26 Int

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.26: an interior operator determines a unique topology. -/
theorem topology_from_interiorOperator_4_26 (Int : Set X -> Set X)
    (hInt : IsInteriorOperator_4_25 Int) :
    InteriorOperatorTopologyData_4_26 (X := X) Int := by
  sorry

/-!
Definition 4.27 introduces the boundary.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.27: the boundary of `A` is `closure A \ interior A`. -/
def boundary_4_27 (𝒪 : Set (Set X)) (A : Set X) : Set X :=
  closure_4_1 𝒪 A \ interior_4_19 𝒪 A

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.27: the boundary is closed. -/
theorem boundary_isClosed_4_27 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    IsClosed_1_2 𝒪 (boundary_4_27 𝒪 A) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: the boundary equals the intersection of two closures. -/
theorem boundary_eq_closure_inter_closure_compl_4_28 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) :
    boundary_4_27 𝒪 A = closure_4_1 𝒪 A ∩ closure_4_1 𝒪 Aᶜ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: boundary points meet both a set and its complement in every neighborhood. -/
theorem mem_boundary_iff_neighborhood_4_28 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) :
    x ∈ boundary_4_27 𝒪 A ↔
      ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V ->
        (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: it is enough to test only open neighborhoods for boundary points. -/
theorem mem_boundary_iff_openNeighborhood_4_28 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) :
    x ∈ boundary_4_27 𝒪 A ↔
      ∀ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V ->
        (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: it is enough to test one neighborhood basis for boundary points. -/
theorem mem_boundary_iff_neighborhoodBasis_4_28 (h𝒪 : IsTopology_1_1 X 𝒪)
    (A : Set X) (x : X) (𝒰 : Set (Set X))
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰) :
    x ∈ boundary_4_27 𝒪 A ↔
      ∀ V ∈ 𝒰, (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: one suitable neighborhood basis characterizes boundary points. -/
theorem mem_boundary_iff_exists_neighborhoodBasis_4_28
    (A : Set X) (x : X) :
    x ∈ boundary_4_27 𝒪 A ↔
      ∃ 𝒰 : Set (Set X), IsNeighborhoodBasis_2_5 𝒪 x 𝒰 ∧
        ∀ V ∈ 𝒰, (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  sorry

section BoundaryExamplesPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (1): the closed unit disk in `ℝ²` has interior the open unit disk. -/
theorem interior_closedUnitDisk_R2_4_29_1 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  interior_4_19
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)}
    = {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ < (1 : ℝ)} := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (1): the boundary of the closed unit disk in `ℝ²` is the unit circle. -/
theorem boundary_closedUnitDisk_R2_4_29_1 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  boundary_4_27
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)}
    = {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ = (1 : ℝ)} := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (2): the closed unit disk in the plane `x₃ = 0` has empty interior in `ℝ³`. -/
theorem interior_closedUnitDisk_plane_R3_4_29_2 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  interior_4_19
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}
    = ∅ := by
  sorry

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (2): the boundary of that planar closed unit disk is the whole set. -/
theorem boundary_closedUnitDisk_plane_R3_4_29_2 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  boundary_4_27
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}
    = {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0} := by
  sorry

end BoundaryExamplesPart

end TopologyPart

/-!
The final statements verify that our closure/interior/boundary language agrees
with mathlib's bundled topological notions.
-/

open TopologicalSpace

section CertifyMathlib

variable {X : Type u} (T : TopologicalSpace X)

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our closure agrees with mathlib's `closure`. -/
theorem closure_eq_mathlibClosure_cert (A : Set X) :
    closure_4_1 {U : Set X | @IsOpen X T U} A = closure A := by
  sorry

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our interior agrees with mathlib's `interior`. -/
theorem interior_eq_mathlibInterior_cert (A : Set X) :
    interior_4_19 {U : Set X | @IsOpen X T U} A = interior A := by
  sorry

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our dense subsets agree with mathlib's `Dense`. -/
theorem isDense_iff_mathlibDense_cert (A : Set X) :
    IsDense_4_10 {U : Set X | @IsOpen X T U} A ↔ Dense A := by
  sorry

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our boundary agrees with mathlib's `frontier`. -/
theorem boundary_eq_mathlibFrontier_cert (A : Set X) :
    boundary_4_27 {U : Set X | @IsOpen X T U} A = frontier A := by
  sorry

end CertifyMathlib

end ClosureInterior
end LeanTopology
