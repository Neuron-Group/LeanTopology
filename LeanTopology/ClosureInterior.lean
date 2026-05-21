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

scoped notation:max A "̄[" 𝒪 "]" => closure_4_1 𝒪 A

/-- `A` is always contained in its closure. -/
theorem subset_closure_4_1 (A : Set X) :
    A ⊆ Ā[𝒪] := by
  intro x hx
  simp only [closure_4_1, ClosedSupersets_4_1, mem_sInter, mem_setOf_eq]
  intro F hF
  exact hF.2 hx

/-- The closure is a closed set. -/
theorem closure_isClosed_4_1 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    IsClosed_1_2 𝒪 Ā[𝒪] := by
  apply (closedSet_properties_1_3.mp h𝒪).C3_sInter
  intro F hF; exact hF.left

/-!
Proposition 4.2 records the minimality of closure among closed supersets.
-/
/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.2: every closed superset of `A` contains `closure A`. -/
theorem closure_minimal_4_2 (A F : Set X)
  (hFclosed : IsClosed_1_2 𝒪 F) (hAF : A ⊆ F) :
    Ā[𝒪] ⊆ F := by
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
    (hx : x ∈ Ā[𝒪]) :
      x ∈ F := by
  specialize hx F
  simp only [ClosedSupersets_4_1,
    mem_setOf_eq, and_imp] at hx
  specialize hx hFclosed hAF
  exact hx

/-- ℛℯ𝓂𝒶𝓇𝓀 4.3: a set is closed iff it equals its closure. -/
theorem isClosed_iff_eq_closure_4_3 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
  IsClosed_1_2 𝒪 A
    <-> Ā[𝒪] = A := by
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
    Ā[𝒪] ⊆ A -> IsClosed_1_2 𝒪 A := by
  intro hyp
  have hEq : Ā[𝒪] = A := Subset.antisymm hyp (subset_closure_4_1 A)
  exact (isClosed_iff_eq_closure_4_3 h𝒪 A).2 hEq

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.4: closure is monotone. -/
theorem closure_mono_4_4 {A B : Set X} (hAB : A ⊆ B) :
    Ā[𝒪] ⊆ B̄[𝒪] := by
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
    x ∈ Ā[𝒪]
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
theorem mem_closure_iff_neighborhood_4_5 (A : Set X) (x : X) :
    x ∈ Ā[𝒪]
      <-> ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V -> (A ∩ V).Nonempty := by
  simpa using mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough to test only open neighborhoods. -/
theorem mem_closure_iff_openNeighborhood_4_5 (A : Set X) (x : X) :
    x ∈ Ā[𝒪] <->
      ∀ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V
        -> (A ∩ V).Nonempty := by
  constructor
  · intro hx V Vop
    exact mem_closure_iff_neighborhood_4_5 A x
      |>.mp hx V Vop.left
  · intro hyp
    /- Same with the precede,
      Since neighborhood in precede is exactly open. -/
    refine (mem_closure_iff_neighborhood_4_5 A x).2 ?_
    intro V hV
    rcases hV with ⟨U, Uop, xinU, UsubV⟩
    exact inter_nonempty_of_subset_right_4_5
      (hyp U ⟨neighborhood_of_open_mem Uop xinU, Uop⟩) UsubV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough to test one neighborhood basis. -/
theorem mem_closure_iff_neighborhoodBasis_4_5
  (A : Set X) (x : X) (𝒰 : Set (Set X))
    (h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰) :
      x ∈ Ā[𝒪]
        <-> ∀ V ∈ 𝒰, (A ∩ V).Nonempty := by
  constructor
  · intro hx V hV
    have := h𝒰.isNeighborhood V hV
    exact mem_closure_iff_neighborhood_4_5 A x
      |>.mp hx V this
  · intro hyp
    /-
      Simular with precedes.
      Which means you could find V,
        satisfied x ∈ V ∈ 𝒰
          and V is a subset of previous openneighborhood.
    -/
    refine (mem_closure_iff_neighborhood_4_5 A x).2 ?_
    intro V hV
    rcases h𝒰.hasRefinement V hV with ⟨U, hU𝒰, hUV⟩
    exact inter_nonempty_of_subset_right_4_5 (hyp U hU𝒰) hUV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.5: it is enough that one neighborhood basis meets `A`. -/
theorem mem_closure_iff_exists_neighborhoodBasis_4_5
  (A : Set X) (x : X) :
    x ∈ Ā[𝒪] <->
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
      A x 𝒰 h𝒰 |>.mp hyp
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
    Ā[𝒪] = A := by
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
    Ā[𝒪] = univ := by
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
          have hyc : y ∈ Fᶜ := by
            simp [hFcuniv]
          have hy_not : y ∉ Fᶜ := by simpa [Set.mem_compl_iff] using hy
          exact hy_not hyc
        · intro hy
          simp at hy
      simp [hFempty] at haF

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (2): in the indiscrete space, the empty set has empty closure. -/
theorem closure_empty_indiscrete_4_9_2
  (h𝒪 : 𝒪 = indiscreteTopology_1_7 X) :
    (∅ : Set X)̄[𝒪] = ∅ := by
  /- Nothing interesting here. -/
  have hTop : IsTopology_1_1 X 𝒪 :=
    h𝒪 ▸ indiscreteTopology_isTopology_1_7 X
  have hEmptyClosed : IsClosed_1_2 𝒪 (∅ : Set X) := by
    simp [IsClosed_1_2, h𝒪, indiscreteTopology_1_7]
  exact (isClosed_iff_eq_closure_4_3 hTop (∅ : Set X)).mp hEmptyClosed

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.9 (3): in the finite-complement topology, every finite set equals its closure. -/
theorem closure_eq_self_finiteComplement_finite_4_9_3
  (𝒪df : 𝒪 = finiteComplementTopology_1_8 X) {A : Set X} (hA : A.Finite) :
    Ā[𝒪] = A := by
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
    Ā[𝒪] = univ := by
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
  set A' := Ā[inducedTopology_1_17]
  set B := Icc (-1 : ℝ) 1

  have c1 : ∀ x > 1, x ∉ A' := by
    intro x hx
    set U := {x | x > (1 : ℝ)}
    have Uop : U ∈ 𝒪 := by
      simp only [𝒪]
      intro y hy
      refine ⟨y - 1, sub_pos.mpr hy, ?_⟩
      intro z hz
      simp only [openBall_1_14, mem_setOf_eq,
        gt_iff_lt, U] at hz ⊢
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
    /- similar with c1 -/
    intro x hx
    set U := {x | x < (-1 : ℝ)}
    have Uop : U ∈ 𝒪 := by
      intro y hy
      refine ⟨-1 - y, sub_pos.mpr hy, ?_⟩
      intro z hz
      simp only [openBall_1_14,
        mem_setOf_eq, U] at hz ⊢
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
    constructor
    · by_contra hxlt
      exact (c2 x (lt_of_not_ge hxlt)) hx
    · by_contra hxgt
      exact (c1 x (lt_of_not_ge hxgt)) hx
  · intro hx
    rcases hx with ⟨hxL, hxR⟩
    by_cases hx1 : x = 1
    · simpa [A', hx1] using c3
    · by_cases hxneg1 : x = -1
      · simpa [A', hxneg1] using c4
      · have hxA : x ∈ A := by
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
  letI : DistanceSpace_1_12 (E n) := euclideanDistanceSpace_1_12 n
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
    apply mem_closure_iff_neighborhoodBasis_4_5 A x 𝒰 h𝒰 |>.mpr
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
  Ā[𝒪] = univ

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.11: `A` is dense iff every nonempty open set meets `A`. -/
theorem isDense_iff_open_4_11 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
  IsDense_4_10 𝒪 A
    <-> ∀ U : Set X, U ∈ 𝒪 → U.Nonempty → (A ∩ U).Nonempty := by
  constructor
  · intro hA U hU hUne
    rcases hUne with ⟨x, hxU⟩
    have hxCl : x ∈ Ā[𝒪] := by
      rw [hA]
      simp
    exact (mem_closure_iff_openNeighborhood_4_5 A x).mp hxCl U
      ⟨neighborhood_of_open_mem hU hxU, hU⟩
  · intro hU
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact (mem_closure_iff_openNeighborhood_4_5 A x).mpr <| by
      intro V hV
      exact hU V hV.2 ⟨x, (openNeighborhood_iff_2_2 h𝒪 x V).mp hV |>.2⟩

/-!
Example 4.12 and Propositions 4.14–4.15 discuss the relation between density,
separability, and countability axioms.
-/

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.12: the rational-coordinate points are dense in Euclidean space. -/
theorem rationalPoints_dense_euclidean_4_12 (n : ℕ) :
    letI : DistanceSpace_1_12 (E n) := euclideanDistanceSpace_1_12 n
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
  intro hyp

  set 𝒪 := @inducedTopology_1_17 X _
  have h𝒪 : IsTopology_1_1 X 𝒪 := by
    simpa [𝒪] using (inducedTopology_isTopology_1_17 (X := X))

  rcases hyp with ⟨A, A_ctb, hA⟩
  set ℬ : Set (Set X) :=
    Set.range fun p : {a // a ∈ A} × ℕ =>
      openBall_1_14 p.1.1 (1 / (2 * (1 + (p.2 : ℝ))))
  /- Then we try to prove that ℬ is exactly a topological bases -/
  use ℬ
  constructor
  · constructor
    · intro B hB
      rcases hB with ⟨p, rfl⟩
      rcases p with ⟨⟨a, haA⟩, n⟩
      simpa [𝒪, inducedTopology_1_17] using
        (openBall_open_1_16 a (1 / (2 * (1 + (n : ℝ)))))
    · intro U hU x hx
      have : ∃ ε > 0, openBall_1_14 x ε ⊆ U := by
        simpa [𝒪, inducedTopology_1_17, isOpenDistance_1_15] using hU x hx
      rcases this with ⟨r, rpos, B₀subU⟩
      have : ∃ k : ℕ, 1 / (1 + (k : ℝ)) < r := by
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / r)
        refine ⟨k, ?_⟩
        have hk' : (1 / r : ℝ) < 1 + (k : ℝ) := by
          have hk1 : (k : ℝ) < 1 + (k : ℝ) := by linarith
          linarith
        have hkpos : 0 < (1 + (k : ℝ)) := by positivity
        have hmul' := mul_lt_mul_of_pos_right hk' rpos
        have hrec : (1 / r : ℝ) * r = 1 := by
          field_simp [rpos.ne']
        have hmul : 1 < r * (1 + (k : ℝ)) := by
          nlinarith [hmul', hrec]
        rw [div_lt_iff₀ hkpos]
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
      rcases this with ⟨k, hk⟩
      set s : ℝ := 1 / (2 * (1 + (k : ℝ)))
      set B₁ := openBall_1_14 x s
      have : (B₁ ∩ A).Nonempty := by
        have hxCl : x ∈ closure_4_1 𝒪 A := by
          rw [hA]
          simp
        have hB₁open : B₁ ∈ 𝒪 := by
          simpa [B₁, s, 𝒪, inducedTopology_1_17] using openBall_open_1_16 x s
        have hxB₁ : x ∈ B₁ := by
          simp only [B₁, s, openBall_1_14, mem_setOf_eq]
          rw [(DistanceSpace_1_12.D1 x x).mpr rfl]
          positivity
        have hB₁nhd : IsOpenNeighborhood_2_1 𝒪 x B₁ := by
          exact ⟨neighborhood_of_open_mem hB₁open hxB₁, hB₁open⟩
        have hAB₁ : (A ∩ B₁).Nonempty :=
          (mem_closure_iff_openNeighborhood_4_5 A x).mp hxCl B₁ hB₁nhd
        simpa [inter_comm] using hAB₁
      rcases this with ⟨a, haB₁, haA⟩
      set B := openBall_1_14 a s
      use B; refine ⟨?_, ?_, ?_⟩
      · refine ⟨⟨⟨a, haA⟩, k⟩, rfl⟩
      · simp only [openBall_1_14, mem_setOf_eq, B₁, B] at haB₁ ⊢
        rw [DistanceSpace_1_12.D2]
        exact haB₁
      · have : B ⊆ openBall_1_14 x r := by
          dsimp [B]
          apply openBall_subset_openBall_1_14
          have hs : s + s = 1 / (1 + (k : ℝ)) := by
            dsimp [s]
            field_simp
            ring
          have hsr : s + s < r := by
            rw [hs]
            exact hk
          have hxa : DistanceSpace_1_12.dist x a < s := by
            simpa [B₁, openBall_1_14, mem_setOf_eq] using haB₁
          linarith
        exact LE.le.subset λ ⦃a⦄ a_1 ↦ B₀subU (this a_1)
  · haveI : Countable {a // a ∈ A} := A_ctb.to_subtype
    exact Set.countable_range _

end MetricCountabilityPart

section CountabilityExamplesPart

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: every finite-complement space is separable. -/
theorem finiteComplement_separable_4_16 (X : Type u) :
    IsSeparable_4_13 (finiteComplementTopology_1_8 X) := by
  set 𝒪 := finiteComplementTopology_1_8 X
  set h𝒪 : IsTopology_1_1 X 𝒪
    := finiteComplementTopology_isTopology_1_8 X
  by_cases ctb_hyp : Countable X
  · use univ
    constructor
    · simpa [Set.countable_univ_iff] using ctb_hyp
    · unfold IsDense_4_10
      apply Set.eq_univ_iff_forall.mpr
      intro x
      exact subset_closure_4_1 (𝒪 := 𝒪)
        univ (by simp)
  · have : ∃ A : Set X, A.Infinite ∧ A.Countable
      := by
        have hXunc : Uncountable X
          := not_countable_iff.mp ctb_hyp
        have hXinf : (univ : Set X).Infinite
          := Set.infinite_univ_iff.2 inferInstance
        rcases Set.Infinite.exists_subset_countable_infinite hXinf
          with ⟨A, hA, hA_ctb, hA_inf⟩
        refine ⟨A, hA_inf, hA_ctb⟩
    rcases this with ⟨A, A_inf, A_ctb⟩
    use A; constructor
    · assumption
    · have hXunc : Uncountable X
        := not_countable_iff.mp ctb_hyp
      letI : Infinite X := inferInstance
      simpa [IsDense_4_10] using
        closure_eq_univ_finiteComplement_infinite_4_9_3
          (X := X) (𝒪 := 𝒪) rfl A_inf

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: an uncountable finite-complement space is not first countable. -/
theorem uncountable_finiteComplement_not_firstCountable_4_16
  (X : Type u) [Uncountable X] :
    ¬ FirstCountable_2_12 (finiteComplementTopology_1_8 X) := by
  exact uncountable_finiteComplement_not_firstCountable_2_14
    (X := X) Set.not_countable_univ

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.16: an uncountable finite-complement space is not second countable. -/
theorem uncountable_finiteComplement_not_secondCountable_4_16
  (X : Type u) [Uncountable X] :
    ¬ Basis.SecondCountable_3_6 (finiteComplementTopology_1_8 X) := by
  intro hSecond
  exact uncountable_finiteComplement_not_firstCountable_4_16 (X := X)
    (Basis.secondCountable_implies_firstCountable_3_7 hSecond)

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
    ∅̄[𝒪] = ∅ := by
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
    A ⊆ Ā[𝒪] :=
  subset_closure_4_1 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure preserves finite unions. -/
theorem closure_union_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) (A B : Set X) :
    (A ∪ B)̄[𝒪] = Ā[𝒪] ∪ B̄[𝒪] := by
  refine Subset.antisymm_iff.mpr ?_
  constructor
  · have c1 : A ⊆ Ā[𝒪] := closure_extensive_4_17 A
    have c2 : B ⊆ B̄[𝒪] := closure_extensive_4_17 B
    have c3 : A ∪ B ⊆ Ā[𝒪] ∪ B̄[𝒪]
      := union_subset_union c1 c2
    have hAB : IsClosed_1_2 𝒪
      (Ā[𝒪] ∪ B̄[𝒪])
        := by
      apply closedSet_properties_1_3.mp h𝒪 |>.C2_union
      · simp only [mem_setOf_eq]
        exact closure_isClosed_4_1 h𝒪 A
      · simp only [mem_setOf_eq]
        exact closure_isClosed_4_1 h𝒪 B
    exact closure_minimal_4_2 (A ∪ B)
      (Ā[𝒪] ∪ B̄[𝒪]) hAB c3
  · have c1 : Ā[𝒪] ⊆ (A ∪ B)̄[𝒪] := by
      have : A ⊆ A ∪ B := subset_union_left
      exact closure_mono_4_4 this
    have c2 : B̄[𝒪] ⊆ (A ∪ B)̄[𝒪] := by
      have : B ⊆ A ∪ B := subset_union_right
      exact closure_mono_4_4 this
    exact union_subset c1 c2

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: closure is idempotent. -/
theorem closure_idem_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    (Ā[𝒪])̄[𝒪] = Ā[𝒪] := by
  have : IsClosed_1_2 𝒪 Ā[𝒪]
    := closure_isClosed_4_1 h𝒪 A
  exact (isClosed_iff_eq_closure_4_3 h𝒪 Ā[𝒪]).mp this

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.17: the topological closure map satisfies the closure-operator axioms. -/
theorem closure_isClosureOperator_4_17 (h𝒪 : IsTopology_1_1 X 𝒪) :
    IsClosureOperator_4_17 (closure_4_1 𝒪) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold closure_4_1
    have : ∅ ∈ ClosedSupersets_4_1 𝒪 ∅ := by
      simp only [ClosedSupersets_4_1,
        empty_subset, and_true, mem_setOf_eq]
      exact closedSet_properties_1_3.mp h𝒪 |>.C1_empty
    exact subset_eq_empty (λ ⦃_⦄ a ↦ a ∅ this) rfl
  · exact closure_extensive_4_17
  · exact closure_union_4_17 h𝒪
  · exact closure_idem_4_17 h𝒪

/-!
Proposition 4.18 reconstructs a topology from an abstract closure operator.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.18: the topology determined by a closure operator. -/
def topologyFromClosureOperator_4_18 (Cl : Set X -> Set X) : Set (Set X) :=
  {U : Set X | Cl Uᶜ = Uᶜ}

/-- A closure operator is monotone. -/
theorem closureOperator_mono_4_18 {Cl : Set X -> Set X}
    (hCl : IsClosureOperator_4_17 Cl) :
    ∀ A B : Set X, A ⊆ B -> Cl A ⊆ Cl B := by
  intro A B hAB
  apply union_eq_right.mp
  rw [← hCl.C3_union]
  congr
  exact union_eq_right.mpr hAB

/-- If the closed sets of a topology are exactly the fixed points of `Cl`,
then its closure operation is `Cl`. -/
theorem closure_eq_Cl_4_18 {Cl : Set X -> Set X} {𝒪 : Set (Set X)}
  (hclosed : ∀ F : Set X, IsClosed_1_2 𝒪 F ↔ Cl F = F)
    (hCl : IsClosureOperator_4_17 Cl) :
      ∀ A, Ā[𝒪] = Cl A := by
  intro A
  refine Subset.antisymm_iff.mpr ?_
  constructor
  · suffices Cl A ∈ ClosedSupersets_4_1 𝒪 A
      from LE.le.subset fun ⦃_⦄ a ↦ a (Cl A) this
    constructor
    · exact (hclosed (Cl A)).2 (hCl.C4_idem A)
    · exact hCl.C2_extensive A
  · unfold closure_4_1
    suffices ∀ F ∈ ClosedSupersets_4_1 𝒪 A, Cl A ⊆ F
      from subset_sInter this
    intro F hF
    have hFclosed : IsClosed_1_2 𝒪 F := by
      simpa [ClosedSupersets_4_1] using hF.1
    have hAF : A ⊆ F := by
      simpa [ClosedSupersets_4_1] using hF.2
    rw [← (hclosed F).1 hFclosed]
    exact closureOperator_mono_4_18 hCl A F hAF

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.18: closure-operator axioms determine a unique topology. -/
structure ClosureOperatorTopologyData_4_18
    (Cl : Set X -> Set X) (_hCl : IsClosureOperator_4_17 Cl) : Prop where
  isTopology : IsTopology_1_1 X (topologyFromClosureOperator_4_18 Cl)
  closure_eq :
      ∀ A : Set X, closure_4_1 (topologyFromClosureOperator_4_18 Cl) A = Cl A
  unique :
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 ->
        (∀ A : Set X, closure_4_1 𝒪 A = Cl A) ->
          𝒪 = topologyFromClosureOperator_4_18 Cl

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.18: a closure operator determines a unique topology. -/
theorem topology_from_closureOperator_4_18 (Cl : Set X -> Set X)
  (hCl : IsClosureOperator_4_17 Cl) :
    ClosureOperatorTopologyData_4_18 (X := X) Cl hCl := by
  set 𝒪 := topologyFromClosureOperator_4_18 Cl
  have h𝒪 : IsTopology_1_1 X 𝒪 := by
    dsimp [𝒪]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [topologyFromClosureOperator_4_18,
          mem_setOf_eq, compl_empty]
        have : univ ⊆ Cl univ := hCl.C2_extensive univ
        exact eq_univ_of_univ_subset this
      · simp only [topologyFromClosureOperator_4_18,
          mem_setOf_eq, compl_univ]
        exact hCl.C1_empty
      · intro U V hU hV
        simp only [topologyFromClosureOperator_4_18, mem_setOf_eq] at hU hV ⊢
        rw [compl_inter]
        nth_rw 2 [← hU, ← hV]
        exact hCl.C3_union Uᶜ Vᶜ
      · suffices ∀ 𝒮c : Set (Set X),
          (∀ F ∈ 𝒮c, IsClosed_1_2 𝒪 F)
            -> IsClosed_1_2 𝒪 (⋂₀ 𝒮c)
              from by
                intro 𝒮 h𝒮
                have hclosed : ∀ F ∈ Set.image compl 𝒮, IsClosed_1_2 𝒪 F := by
                  intro F hF
                  rcases hF with ⟨U, hU, rfl⟩
                  exact closed_of_open_compl (h𝒮 U hU)
                have hsInterClosed : IsClosed_1_2 𝒪 (⋂₀ Set.image compl 𝒮) :=
                  this (Set.image compl 𝒮) hclosed
                have hopen : (⋂₀ Set.image compl 𝒮)ᶜ ∈ 𝒪 := hsInterClosed
                have hEq : (⋂₀ Set.image compl 𝒮)ᶜ = ⋃₀ 𝒮 := by
                  ext x
                  simp
                rwa [hEq] at hopen
        intro 𝒮c h𝒮c
        suffices Cl (⋂₀ 𝒮c) = ⋂₀ 𝒮c from by
          unfold IsClosed_1_2
          simp only [topologyFromClosureOperator_4_18,
            mem_setOf_eq, compl_compl, 𝒪]
          assumption
        refine Subset.antisymm_iff.mpr ?_
        constructor
        · have : ∀ F ∈ 𝒮c, Cl (⋂₀ 𝒮c) ⊆ F := by
            intro F hF
            have : ⋂₀ 𝒮c ⊆ F
              := sInter_subset_of_mem hF
            have : Cl (⋂₀ 𝒮c) ⊆ Cl F
              := closureOperator_mono_4_18 hCl (⋂₀ 𝒮c) F this
            specialize h𝒮c F hF
            simp only [IsClosed_1_2,
              topologyFromClosureOperator_4_18,
              mem_setOf_eq, compl_compl, 𝒪] at h𝒮c
            rw [← h𝒮c]
            assumption
          exact subset_sInter this
        · exact hCl.C2_extensive (⋂₀ 𝒮c)
  have hclosed_𝒪 : ∀ F : Set X, IsClosed_1_2 𝒪 F ↔ Cl F = F := by
    intro F
    simp [IsClosed_1_2, topologyFromClosureOperator_4_18, 𝒪]
  have closure_eq_Cl : ∀ A, closure_4_1 𝒪 A = Cl A :=
    closure_eq_Cl_4_18 hclosed_𝒪 hCl
  refine ⟨?_, ?_, ?_⟩
  · exact h𝒪
  · exact closure_eq_Cl
  · intro 𝒪₁ h𝒪₁ hyp
    have hclosed_𝒪₁ : ∀ F : Set X, IsClosed_1_2 𝒪₁ F ↔ Cl F = F := by
      intro F
      constructor
      · intro hFclosed
        rw [← hyp F]
        exact isClosed_iff_eq_closure_4_3 h𝒪₁ F
          |>.mp hFclosed
      · intro hFfix
        exact isClosed_iff_eq_closure_4_3 h𝒪₁ F
          |>.mpr ((hyp F).trans hFfix)
    have closure_eq_Cl_𝒪₁ : ∀ A : Set X, closure_4_1 𝒪₁ A = Cl A :=
      closure_eq_Cl_4_18 hclosed_𝒪₁ hCl
    ext U; constructor
    · intro Uop
      simp only [topologyFromClosureOperator_4_18, mem_setOf_eq]
      have := closure_eq_Cl_𝒪₁ Uᶜ
      rw [← this]
      suffices IsClosed_1_2 𝒪₁ Uᶜ
        from isClosed_iff_eq_closure_4_3 h𝒪₁ Uᶜ
          |>.mp this
      simp only [IsClosed_1_2, compl_compl]
      assumption
    · intro hU
      simp only [topologyFromClosureOperator_4_18, mem_setOf_eq] at hU
      specialize hyp Uᶜ
      rw [← hyp] at hU
      have : IsClosed_1_2 𝒪₁ Uᶜ
        := isClosed_iff_eq_closure_4_3 h𝒪₁ Uᶜ
          |>.mpr hU
      exact isClosed_compl_iff_open U |>.mp this

/-!
Definition 4.19 introduces interior as the union of all open subsets.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.19: the family of open subsets of `A`. -/
def OpenSubsets_4_19 (𝒪 : Set (Set X)) (A : Set X) : Set (Set X) :=
  {U : Set X | U ∈ 𝒪 ∧ U ⊆ A}

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.19: the interior of `A` is the union of all open subsets of `A`. -/
def interior_4_19 (𝒪 : Set (Set X)) (A : Set X) : Set X :=
  ⋃₀ OpenSubsets_4_19 𝒪 A

scoped notation:max A "ᵒ[" 𝒪 "]" => interior_4_19 𝒪 A

/-- Interior is open. -/
theorem interior_isOpen_4_19 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    Aᵒ[𝒪] ∈ 𝒪 := by
  set 𝒮 := {U | U ∈ 𝒪 ∧ U ⊆ A}
  have h𝒮 : ∀ U ∈ 𝒮, U ∈ 𝒪 := by
    intro U hU;
    simp [𝒮] at hU
    exact hU.left
  exact h𝒪.O3_sUnion 𝒮 h𝒮

/-- Interior is contained in the original set. -/
theorem interior_subset_4_19 (A : Set X) :
    Aᵒ[𝒪] ⊆ A := by
  intro x hx
  rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
  exact hU.2 hxU

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.20: every open subset of `A` lies in `interior A`. -/
theorem interior_maximal_4_20 (A U : Set X)
  (hUopen : U ∈ 𝒪) (hUA : U ⊆ A) :
    U ⊆ Aᵒ[𝒪] := by
  suffices U ∈ OpenSubsets_4_19 𝒪 A
    from subset_sUnion_of_subset
      (OpenSubsets_4_19 𝒪 A) U
        (λ ⦃_⦄ ↦ id) this
  exact ⟨hUopen, hUA⟩

/-- ℛℯ𝓂𝒶𝓇𝓀 4.21: a set is open iff it equals its interior. -/
theorem isOpen_iff_eq_interior_4_21 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    A ∈ 𝒪 <-> Aᵒ[𝒪] = A := by
  constructor<;>intro hyp
  · apply Subset.antisymm_iff.mpr
    constructor
    · exact interior_subset_4_19 A
    · exact interior_maximal_4_20
        A A hyp λ ⦃_⦄ ↦ id
  · rw [← hyp]
    exact interior_isOpen_4_19 h𝒪 A

/-- ℛℯ𝓂𝒶𝓇𝓀 4.21: equivalently, a set is open iff it is contained in its interior. -/
theorem isOpen_iff_subset_interior_4_21 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    A ∈ 𝒪 <-> A ⊆ Aᵒ[𝒪] := by
  rw [isOpen_iff_eq_interior_4_21 h𝒪 A]
  constructor
  · intro hEq
    rw [hEq]
  · intro hSub
    exact Subset.antisymm (interior_subset_4_19 A) hSub

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: the complement of the interior is the closure of the complement. -/
theorem compl_interior_eq_closure_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    (Aᵒ[𝒪])ᶜ = closure_4_1 𝒪 Aᶜ := by
  apply Subset.antisymm_iff.mpr
  constructor
  · suffices (closure_4_1 𝒪 Aᶜ)ᶜ ⊆ Aᵒ[𝒪]
      from compl_subset_comm.mp this
    apply interior_maximal_4_20
    · have : closure_4_1 𝒪 Aᶜ |> IsClosed_1_2 𝒪
        := closure_isClosed_4_1 h𝒪 Aᶜ
      exact open_of_closed_compl this
    · suffices Aᶜ ⊆ closure_4_1 𝒪 Aᶜ
       from compl_subset_comm.mp this
      exact closure_extensive_4_17 Aᶜ
  · suffices IsClosed_1_2 𝒪 (Aᵒ[𝒪])ᶜ ∧ Aᶜ ⊆ (Aᵒ[𝒪])ᶜ
      from LE.le.subset λ ⦃_⦄ a ↦ a (Aᵒ[𝒪])ᶜ this
    constructor
    · simp only [IsClosed_1_2, compl_compl]
      exact interior_isOpen_4_19 h𝒪 A
    · suffices Aᵒ[𝒪] ⊆ A
        from compl_subset_compl_of_subset this
      exact interior_subset_4_19 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: dually, closure is the complement of the interior of the complement. -/
theorem closure_eq_compl_interior_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    closure_4_1 𝒪 A = (Aᶜ)ᵒ[𝒪]ᶜ := by
  have := compl_interior_eq_closure_compl_4_22 h𝒪 Aᶜ
  rw [compl_compl] at this
  exact this.symm

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.22: equivalently,
  the interior is the complement of the closure of the complement. -/
theorem interior_eq_compl_closure_compl_4_22 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    Aᵒ[𝒪] = (closure_4_1 𝒪 Aᶜ)ᶜ := by
  have := compl_interior_eq_closure_compl_4_22 h𝒪 A
  exact eq_compl_comm.mp (id (Eq.symm this))

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.23: interior is monotone. -/
theorem interior_mono_4_23 {A B : Set X} (hAB : A ⊆ B) :
    Aᵒ[𝒪] ⊆ Bᵒ[𝒪] := by
  intro x hx
  rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
  apply mem_sUnion.mpr
  use U
  constructor
  · exact ⟨hU.1, hU.2.trans hAB⟩
  · exact hxU

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: interior points are exactly those admitting a neighborhood inside `A`. -/
theorem mem_interior_iff_neighborhood_4_24'
    (A : Set X) (x : X) :
    x ∈ Aᵒ[𝒪] <-> ∃ V : Set X, IsNeighborhood_2_1 𝒪 x V ∧ V ⊆ A := by
  constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
    exact ⟨U, neighborhood_of_open_mem hU.1 hxU, hU.2⟩
  · rintro ⟨V, hV, hVA⟩
    rcases hV with ⟨U, hUopen, hxU, hUV⟩
    exact interior_maximal_4_20 A U hUopen (hUV.trans hVA) hxU

/-- 𝒫𝓇ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: interior points are exactly those admitting a neighborhood inside `A`. -/
theorem mem_interior_iff_neighborhood_4_24 (A : Set X) (x : X) :
    x ∈ Aᵒ[𝒪] <-> ∃ V : Set X, IsNeighborhood_2_1 𝒪 x V ∧ V ⊆ A := by
  simpa using mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: equivalently, one may use an open neighborhood contained in `A`. -/
theorem mem_interior_iff_openNeighborhood_4_24 (A : Set X) (x : X) :
    x ∈ Aᵒ[𝒪] ↔ ∃ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V ∧ V ⊆ A := by
  constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨V, hV, hxV⟩
    exact ⟨V, ⟨neighborhood_of_open_mem hV.1 hxV, hV.1⟩, hV.2⟩
  · rintro ⟨V, hV, hVA⟩
    exact (mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x).2 ⟨V, hV.1, hVA⟩

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.24: equivalently, `A` itself is a neighborhood of `x`. -/
theorem mem_interior_iff_isNeighborhood_4_24 (A : Set X) (x : X) :
    x ∈ Aᵒ[𝒪] ↔ IsNeighborhood_2_1 𝒪 x A := by
  constructor
  · intro hx
    rcases (mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x).mp hx with ⟨V, hV, hVA⟩
    rcases hV with ⟨U, hUopen, hxU, hUV⟩
    exact ⟨U, hUopen, hxU, hUV.trans hVA⟩
  · intro hA
    exact (mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x).2 ⟨A, hA, Subset.rfl⟩

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior of the whole space. -/
theorem interior_univ_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) :
    (univ : Set X)ᵒ[𝒪] = univ := by
  unfold interior_4_19
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    apply mem_sUnion.mpr
    use univ
    constructor
    · simp only [OpenSubsets_4_19, subset_univ, and_true, setOf_mem_eq]
      exact h𝒪.O1_univ
    · exact mem_univ x

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior is contractive. -/
theorem interior_contractive_4_25 (A : Set X) :
    Aᵒ[𝒪] ⊆ A :=
  interior_subset_4_19 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior preserves finite intersections. -/
theorem interior_inter_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) (A B : Set X) :
    (A ∩ B)ᵒ[𝒪] = Aᵒ[𝒪] ∩ Bᵒ[𝒪] := by
  repeat rw [interior_eq_compl_closure_compl_4_22 h𝒪]
  rw [← compl_union]; congr; rw [compl_inter]
  exact closure_union_4_17 h𝒪 Aᶜ Bᶜ

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: interior is idempotent. -/
theorem interior_idem_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    (Aᵒ[𝒪])ᵒ[𝒪] = Aᵒ[𝒪] := by
  have : Aᵒ[𝒪] ∈ 𝒪 := interior_isOpen_4_19 h𝒪 A
  exact isOpen_iff_eq_interior_4_21 h𝒪 Aᵒ[𝒪] |>.mp this

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.25: an abstract interior operator on `P(X)`. -/
structure IsInteriorOperator_4_25 (Int : Set X -> Set X) : Prop where
  I1_univ : Int univ = univ
  I2_contractive : ∀ A : Set X, Int A ⊆ A
  I3_inter : ∀ A B : Set X, Int (A ∩ B) = Int A ∩ Int B
  I4_idem : ∀ A : Set X, Int (Int A) = Int A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.25: the topological interior map satisfies the interior-operator axioms. -/
theorem interior_isInteriorOperator_4_25 (h𝒪 : IsTopology_1_1 X 𝒪) :
    IsInteriorOperator_4_25 (interior_4_19 𝒪) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact interior_univ_4_25 h𝒪
  · exact λ A   ↦ interior_contractive_4_25 A
  · exact λ A B ↦ interior_inter_4_25 h𝒪    A B
  · exact λ A   ↦ interior_idem_4_25  h𝒪    A

/-!
Proposition 4.26 reconstructs a topology from an abstract interior operator.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.26: the topology determined by an interior operator. -/
def topologyFromInteriorOperator_4_26 (Int : Set X -> Set X) : Set (Set X) :=
  {U : Set X | Int U = U}

/-- An interior operator is monotone. -/
theorem interiorOperator_mono_4_26 {Int : Set X -> Set X}
  (hInt : IsInteriorOperator_4_25 Int) :
    ∀ A B : Set X, A ⊆ B -> Int A ⊆ Int B := by
  intro A B hAB
  have hEq : Int A ∩ Int B = Int A := by
    calc
      Int A ∩ Int B = Int (A ∩ B) := by
        rw [hInt.I3_inter]
      _ = Int A := by
        congr
        exact inter_eq_left.mpr hAB
  exact inter_eq_left.mp hEq

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.26: interior-operator axioms determine a unique topology. -/
structure InteriorOperatorTopologyData_4_26
    (Int : Set X -> Set X) (_hInt : IsInteriorOperator_4_25 Int) : Prop where
  isTopology : IsTopology_1_1 X (topologyFromInteriorOperator_4_26 Int)
  interior_eq :
      ∀ A : Set X, Aᵒ[topologyFromInteriorOperator_4_26 Int] = Int A
  unique :
      ∀ 𝒪 : Set (Set X), IsTopology_1_1 X 𝒪 ->
        (∀ A : Set X, Aᵒ[𝒪] = Int A) ->
          𝒪 = topologyFromInteriorOperator_4_26 Int

theorem interior_eq_Int_4_26 {Int : Set X -> Set X} {𝒪 : Set (Set X)}
  (hop : ∀ U, U ∈ 𝒪 ↔ Int U = U) (hInt : IsInteriorOperator_4_25 Int) :
    ∀ A, Aᵒ[𝒪] = Int A := by
  intro A
  simp only [interior_4_19]
  apply Subset.antisymm
  · suffices ∀ S ∈ OpenSubsets_4_19 𝒪 A, S ⊆ Int A
      from sUnion_subset this
    simp only [OpenSubsets_4_19, mem_setOf_eq, and_imp]
    intro S Sop SsubA
    specialize hop S
    rcases hop with ⟨hop, _⟩
    specialize hop Sop
    rw [← hop]
    exact interiorOperator_mono_4_26 hInt S A SsubA
  · suffices Int A ∈ OpenSubsets_4_19 𝒪 A
      from subset_sUnion_of_subset
        (OpenSubsets_4_19 𝒪 A) (Int A) (λ ⦃_⦄ ↦ id) this
    constructor
    · exact hop (Int A) |>.mpr (hInt.I4_idem A)
    · exact hInt.I2_contractive A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.26: an interior operator determines a unique topology. -/
theorem topology_from_interiorOperator_4_26 (Int : Set X -> Set X)
  (hInt : IsInteriorOperator_4_25 Int) :
    InteriorOperatorTopologyData_4_26 (X := X) Int hInt := by
  set 𝒪 := topologyFromInteriorOperator_4_26 Int
  have h𝒪 : IsTopology_1_1 X 𝒪 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    <;> simp only [topologyFromInteriorOperator_4_26, mem_setOf_eq, 𝒪]
    · apply Subset.antisymm
      · exact hInt.I2_contractive ∅
      · exact empty_subset (Int ∅)
    · exact hInt.I1_univ
    · intro U V hU hV
      nth_rw 2 [← hU, ← hV]
      exact hInt.I3_inter U V
    · intro 𝒮 h𝒮
      apply Subset.antisymm
      · exact hInt.I2_contractive (⋃₀ 𝒮)
      · suffices ∀ S ∈ 𝒮, S ⊆ Int (⋃₀ 𝒮)
          from sUnion_subset this
        intro S hS
        specialize h𝒮 S hS
        rw [← h𝒮]
        apply interiorOperator_mono_4_26 hInt
        exact subset_sUnion_of_subset 𝒮 S
          (λ ⦃_⦄ ↦ id) hS
  refine ⟨?_, ?_, ?_⟩
  · trivial
  · exact interior_eq_Int_4_26 (𝒪 := 𝒪) (by
      intro U
      simp [𝒪, topologyFromInteriorOperator_4_26]) hInt
  · intro 𝒪₁ h𝒪₁ hyp
    change 𝒪₁ = 𝒪
    ext U
    constructor
    · intro Uop₁
      specialize hyp U
      simp only [topologyFromInteriorOperator_4_26, mem_setOf_eq, 𝒪]
      rw [← hyp]
      exact isOpen_iff_eq_interior_4_21 h𝒪₁ U
        |>.mp Uop₁
    · intro Uop
      specialize hyp U
      rw [← Uop, ← hyp]
      exact interior_isOpen_4_19 h𝒪₁ U

/-!
Definition 4.27 introduces the boundary.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.27: the boundary of `A` is `closure A \ interior A`. -/
def boundary_4_27 (𝒪 : Set (Set X)) (A : Set X) : Set X :=
  Ā[𝒪] \ Aᵒ[𝒪]

scoped notation:max "∂[" 𝒪 "] " A => boundary_4_27 𝒪 A

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 4.27: the boundary is closed. -/
theorem boundary_isClosed_4_27 (h𝒪 : IsTopology_1_1 X 𝒪) (A : Set X) :
    IsClosed_1_2 𝒪 (∂[𝒪] A) := by
  simp only [IsClosed_1_2, boundary_4_27, compl_diff]
  suffices Aᵒ[𝒪] ∈ 𝒪 ∧ Ā[𝒪]ᶜ ∈ 𝒪
    from by
      rcases this with ⟨hInt, hCl⟩
      exact h𝒪.O2_union hInt hCl
  constructor
  · exact interior_isOpen_4_19 h𝒪 A
  · suffices IsClosed_1_2 𝒪 Ā[𝒪]
      from open_of_closed_compl this
    exact closure_isClosed_4_1 h𝒪 A

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: the boundary equals the intersection of two closures. -/
theorem boundary_eq_closure_inter_closure_compl_4_28 (h𝒪 : IsTopology_1_1 X 𝒪)
  (A : Set X) :
    (∂[𝒪] A) = Ā[𝒪] ∩ closure_4_1 𝒪 Aᶜ := by
  have : Aᵒ[𝒪] = (Aᶜ̄[𝒪])ᶜ
    := interior_eq_compl_closure_compl_4_22 h𝒪 A
  unfold boundary_4_27
  rw [this]
  exact diff_compl

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: boundary points meet both a set and its complement in every neighborhood. -/
theorem mem_boundary_iff_neighborhood_4_28'
  (A : Set X) (x : X) :
    x ∈ (∂[𝒪] A) <->
      ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V ->
        (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  constructor
  · rintro ⟨hxcl, hxint⟩ V hV
    constructor
    · exact (mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x).mp hxcl V hV
    · by_contra hEmpty
      have hNotInt : ¬ x ∈ Aᵒ[𝒪] := by
        intro hxInt
        exact hxint hxInt
      exact hNotInt <|
        (mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x).2
          ⟨V, hV, by
            simpa using compl_subset_comm.mp <|
              (inter_empty_iff_subset_compl_right).mp
                (not_nonempty_iff_eq_empty.mp hEmpty)⟩
  · intro hyp
    constructor
    · exact (mem_closure_iff_neighborhood_4_5' (𝒪 := 𝒪) A x).2
        (fun V hV => (hyp V hV).1)
    · intro hxInt
      rcases (mem_interior_iff_neighborhood_4_24' (𝒪 := 𝒪) A x).mp hxInt with ⟨V, hV, hVA⟩
      rcases hyp V hV with ⟨_, hAcV⟩
      rcases hAcV with ⟨y, hyAcompl, hyV⟩
      exact hyAcompl (hVA hyV)

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: boundary points meet both a set and its complement in every neighborhood. -/
theorem mem_boundary_iff_neighborhood_4_28 (A : Set X) (x : X) :
    x ∈ (∂[𝒪] A) <->
      ∀ V : Set X, IsNeighborhood_2_1 𝒪 x V ->
        (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  simpa using mem_boundary_iff_neighborhood_4_28' (𝒪 := 𝒪) A x

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: it is enough to test only open neighborhoods for boundary points. -/
theorem mem_boundary_iff_openNeighborhood_4_28 (A : Set X) (x : X) :
    x ∈ (∂[𝒪] A) <->
      ∀ V : Set X, IsOpenNeighborhood_2_1 𝒪 x V ->
        (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  constructor
  · intro hx V hV
    exact (mem_boundary_iff_neighborhood_4_28 A x).mp hx V hV.left
  · intro hyp
    refine (mem_boundary_iff_neighborhood_4_28 A x).2 ?_
    intro V hV
    rcases hV with ⟨U, Uop, xinU, UsubV⟩
    rcases hyp U ⟨neighborhood_of_open_mem Uop xinU, Uop⟩ with ⟨hAU, hAcU⟩
    constructor
    · exact inter_nonempty_of_subset_right_4_5 hAU UsubV
    · exact inter_nonempty_of_subset_right_4_5 hAcU UsubV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: it is enough to test one neighborhood basis for boundary points. -/
theorem mem_boundary_iff_neighborhoodBasis_4_28
  (A : Set X) (x : X) (𝒰 : Set (Set X))
  (h𝒰 : IsNeighborhoodBasis_2_5 𝒪 x 𝒰) :
      x ∈ (∂[𝒪] A) <->
        ∀ V ∈ 𝒰, (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  constructor
  · intro hx V hV
    exact (mem_boundary_iff_neighborhood_4_28 A x).mp hx V (h𝒰.isNeighborhood V hV)
  · intro hyp
    refine (mem_boundary_iff_neighborhood_4_28 A x).2 ?_
    intro V hV
    rcases h𝒰.hasRefinement V hV with ⟨U, hU𝒰, hUV⟩
    rcases hyp U hU𝒰 with ⟨hAU, hAcU⟩
    constructor
    · exact inter_nonempty_of_subset_right_4_5 hAU hUV
    · exact inter_nonempty_of_subset_right_4_5 hAcU hUV

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 4.28: one suitable neighborhood basis characterizes boundary points. -/
theorem mem_boundary_iff_exists_neighborhoodBasis_4_28
  (A : Set X) (x : X) :
    x ∈ (∂[𝒪] A) ↔
      ∃ 𝒰 : Set (Set X), IsNeighborhoodBasis_2_5 𝒪 x 𝒰 ∧
        ∀ V ∈ 𝒰, (A ∩ V).Nonempty ∧ (Aᶜ ∩ V).Nonempty := by
  constructor
  · intro hx
    refine ⟨{V : Set X | IsNeighborhood_2_1 𝒪 x V},
      allNeighborhoods_isNeighborhoodBasis_2_6 x, ?_⟩
    intro V hV
    exact (mem_boundary_iff_neighborhood_4_28' (𝒪 := 𝒪) A x).mp hx V (mem_setOf.mp hV)
  · rintro ⟨𝒰, h𝒰, hA𝒰⟩
    refine (mem_boundary_iff_neighborhood_4_28' (𝒪 := 𝒪) A x).2 ?_
    intro V hV
    rcases h𝒰.hasRefinement V hV with ⟨U, hU𝒰, hUV⟩
    rcases hA𝒰 U hU𝒰 with ⟨hAU, hAcU⟩
    constructor
    · exact inter_nonempty_of_subset_right_4_5 hAU hUV
    · exact inter_nonempty_of_subset_right_4_5 hAcU hUV

section BoundaryExamplesPart

private theorem closedUnitDisk_plane_R3_isClosed :
    letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
      euclideanDistanceSpace_1_12 3
    IsClosed_1_2
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  let A : Set (LeanTopology.EuclideanSpaceTopology.E 3) :=
    {x : LeanTopology.EuclideanSpaceTopology.E 3 |
      x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}
  let B : Set (LeanTopology.EuclideanSpaceTopology.E 3) := closedBall_1_14 0 1
  let P : Set (LeanTopology.EuclideanSpaceTopology.E 3) := {x | x 2 = 0}
  have hB : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›) B :=
    closedBall_closed_1_16 0 1
  have hP : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›) P := by
    change isOpenDistance_1_15 Pᶜ
    intro x hx
    have hx2 : x 2 ≠ 0 := by
      simpa [P] using hx
    refine ⟨|x 2|, by simpa [abs_pos] using hx2, ?_⟩
    intro y hy
    have hylt : dist x y < |x 2| := by
      simpa [openBall_1_14] using hy
    have hy2 : y 2 ≠ 0 := by
      intro hy20
      have hs : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
        simpa [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq (x - y)
      have hcoord : |x 2 - y 2| ≤ dist x y := by
        have hsqle : (x 2 - y 2) ^ 2 ≤ ‖x - y‖ ^ 2 := by
          nlinarith [hs, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
        have hcoord' : |x 2 - y 2| ≤ ‖x - y‖ := by
          simpa [abs_of_nonneg (norm_nonneg (x - y))] using (sq_le_sq.mp hsqle)
        simpa [dist_eq_norm] using hcoord'
      have hEqAbs : |x 2| = |x 2 - y 2| := by
        simp [hy20]
      have : |x 2| ≤ dist x y := by
        rw [hEqAbs]
        exact hcoord
      exact (not_lt_of_ge this) hylt
    simpa [P] using hy2
  have hAeq : A = B ∩ P := by
    ext x
    constructor
    · intro hx
      constructor
      · change dist 0 x ≤ (1 : ℝ)
        rw [dist_comm, dist_eq_norm, sub_zero]
        have hx' := hx.1
        have hs : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
          simpa [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq x
        rw [hx.2] at hs
        have hxnonneg : 0 ≤ ‖x‖ := norm_nonneg x
        have hsq : ‖x‖ ^ 2 ≤ 1 := by
          nlinarith [hx', hs]
        nlinarith
      · exact hx.2
    · rintro ⟨hxB, hxP⟩
      constructor
      · change dist 0 x ≤ (1 : ℝ) at hxB
        rw [dist_comm, dist_eq_norm, sub_zero] at hxB
        have hs : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
          simpa [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq x
        rw [hxP] at hs
        have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [hxB, norm_nonneg x]
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hs, hsq]
      · exact hxP
  have hAclosed' : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›) (B ∩ P) :=
    inducedTopology_isTopology_1_17.C3_inter hB hP
  have : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›) A := hAeq.symm ▸ hAclosed'
  simpa [A] using this

private theorem closure_closedUnitDisk_plane_R3 :
    letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
      euclideanDistanceSpace_1_12 3
    closure_4_1
      (@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›)
      {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}
      = {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  exact (isClosed_iff_eq_closure_4_3 inducedTopology_isTopology_1_17 _).mp
    closedUnitDisk_plane_R3_isClosed

private theorem interior_closedUnitDisk_R2_subset :
    letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
      euclideanDistanceSpace_1_12 2
    {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)}ᵒ[
        @inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›]
      ⊆ {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ < (1 : ℝ)} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  let A : Set (LeanTopology.EuclideanSpaceTopology.E 2) := {x | ‖x‖ ≤ (1 : ℝ)}
  intro x hx
  by_cases hlt : ‖x‖ < (1 : ℝ)
  · exact hlt
  · have hxA : x ∈ A := interior_contractive_4_25 (𝒪 := @inducedTopology_1_17 _ ‹_›) A hx
    have hxle : ‖x‖ ≤ (1 : ℝ) := by simpa [A] using hxA
    have hxeq : ‖x‖ = (1 : ℝ) := le_antisymm hxle (le_of_not_gt hlt)
    rcases (mem_interior_iff_openNeighborhood_4_24 A x).mp hx
      with ⟨V, hV, hVA⟩
    rcases hV with ⟨hVn, hVopen⟩
    obtain ⟨W, hW, hWV⟩ := (distance_openBall_isNeighborhoodBasis_2_8 x).hasRefinement V hVn
    rcases hW with ⟨r, hr, rfl⟩
    let y : LeanTopology.EuclideanSpaceTopology.E 2 := (1 + r / 2) • x
    have hyr : y ∈ openBall_1_14 x r := by
      have hyx : x - y = (-r / 2) • x := by
        ext i
        simp [y]
        ring
      have hdist : dist x y = r / 2 := by
        rw [dist_eq_norm, hyx, norm_smul]
        have hr2 : 0 ≤ r / 2 := by linarith
        have hnorm : ‖(-r) / 2‖ = r / 2 := by
          rw [show (-r) / 2 = -(r / 2) by ring, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr2]
        calc
          ‖(-r) / 2‖ * ‖x‖ = (r / 2) * 1 := by
            rw [hnorm, hxeq]
          _ = r / 2 := by ring
      have hlt' : r / 2 < r := by linarith
      change dist x y < r
      rw [hdist]
      exact hlt'
    have hyA : y ∈ A := hVA (hWV hyr)
    have hynotA : y ∉ A := by
      have hygt : 1 < ‖y‖ := by
        change 1 < ‖(1 + r / 2) • x‖
        rw [norm_smul, hxeq]
        have hpos : 0 ≤ 1 + r / 2 := by linarith
        calc
          1 < (1 + r / 2) * 1 := by linarith
          _ = ‖1 + r / 2‖ * 1 := by
            rw [Real.norm_of_nonneg hpos]
      intro hyA'
      have hyle : ‖y‖ ≤ 1 := by simpa [A] using hyA'
      linarith
    exact False.elim (hynotA hyA)

private theorem openUnitDisk_R2_subset_interior :
    letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
      euclideanDistanceSpace_1_12 2
    {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ < (1 : ℝ)}
      ⊆ {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)}ᵒ[
        @inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›] := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  let A : Set (LeanTopology.EuclideanSpaceTopology.E 2) := {x | ‖x‖ ≤ (1 : ℝ)}
  intro x hx
  refine (mem_interior_iff_neighborhood_4_24'
    (𝒪 := @inducedTopology_1_17 _ ‹_›) A x).2 ?_
  refine ⟨openBall_1_14 x (1 - ‖x‖), ?_, ?_⟩
  · refine (distance_openBall_isNeighborhoodBasis_2_8 x).isNeighborhood _ ?_
    refine ⟨1 - ‖x‖, ?_, rfl⟩
    have : 0 < 1 - ‖x‖ := by
      simpa using hx
    exact this
  · intro y hy
    simp only [mem_setOf_eq, A] at ⊢
    have hy' : dist y x < 1 - ‖x‖ := by
      simpa [openBall_1_14, dist_comm] using hy
    have hnorm : ‖y - x‖ < 1 - ‖x‖ := by
      simpa [dist_eq_norm] using hy'
    have : ‖y‖ < (1 : ℝ) := by
      calc
      ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_comm] using norm_triangle_0_2 (y - x) x
      _ < (1 - ‖x‖) + ‖x‖ := by
        linarith
      _ = (1 : ℝ) := by ring
    exact this.le

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (1): the closed unit disk in `ℝ²` has interior the open unit disk. -/
theorem interior_closedUnitDisk_R2_4_29_1 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)}ᵒ[
      @inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›]
    = {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ < (1 : ℝ)} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  exact Subset.antisymm interior_closedUnitDisk_R2_subset openUnitDisk_R2_subset_interior

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (1): the boundary of the closed unit disk in `ℝ²` is the unit circle. -/
theorem boundary_closedUnitDisk_R2_4_29_1 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  (∂[@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 2) ‹_›]
      {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ ≤ (1 : ℝ)})
    = {x : LeanTopology.EuclideanSpaceTopology.E 2 | ‖x‖ = (1 : ℝ)} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 2) :=
    euclideanDistanceSpace_1_12 2
  let A : Set (LeanTopology.EuclideanSpaceTopology.E 2) := {x | ‖x‖ ≤ (1 : ℝ)}
  rw [boundary_4_27]
  have hAclosed : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›) A := by
    have hclosedBall : IsClosed_1_2 (@inducedTopology_1_17 _ ‹_›)
        ({x : LeanTopology.EuclideanSpaceTopology.E 2 | dist 0 x ≤ (1 : ℝ)}) :=
      closedBall_closed_1_16 (0 : LeanTopology.EuclideanSpaceTopology.E 2) 1
    simpa [A, dist_eq_norm] using hclosedBall
  have hAcl : Ā[@inducedTopology_1_17 _ ‹_›] = A :=
    (isClosed_iff_eq_closure_4_3 inducedTopology_isTopology_1_17 A).mp hAclosed
  rw [hAcl]
  rw [interior_closedUnitDisk_R2_4_29_1]
  ext x
  simp only [mem_diff, mem_setOf_eq, not_lt, A]
  constructor
  · intro hx
    linarith
  · intro hx
    constructor
    · linarith
    · linarith

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (2): the closed unit disk in the plane `x₃ = 0` has empty interior in `ℝ³`. -/
theorem interior_closedUnitDisk_plane_R3_4_29_2 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}ᵒ[
      @inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›]
    = ∅ := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  let A : Set (LeanTopology.EuclideanSpaceTopology.E 3) :=
    {x : LeanTopology.EuclideanSpaceTopology.E 3 |
      x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0}
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases (mem_interior_iff_neighborhood_4_24'
    (𝒪 := @inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›)
    A x).mp hx with ⟨V, hV, hVA⟩
  obtain ⟨W, hW, hWV⟩ :=
    (distance_openBall_isNeighborhoodBasis_2_8 x).hasRefinement V hV
  rcases hW with ⟨r, hr, rfl⟩
  have hxA : x ∈ A := by
    rcases hV with ⟨U, hU, hxU, hUV⟩
    exact hVA (hUV hxU)
  have hx2 : x 2 = 0 := hxA.2
  have hyr : x + EuclideanSpace.single (2 : Fin 3) (r / 2) ∈ openBall_1_14 x r := by
    have hd : dist x (x + EuclideanSpace.single (2 : Fin 3) (r / 2)) = |r| / 2 := by
      rw [dist_eq_norm]
      simp [EuclideanSpace.single]
    have : dist x (x + EuclideanSpace.single (2 : Fin 3) (r / 2)) < r := by
      rw [hd]
      rw [abs_of_nonneg hr.le]
      linarith
    exact this
  have hyA : x + EuclideanSpace.single (2 : Fin 3) (r / 2) ∈ A := hVA (hWV hyr)
  have hy2ne : (x + EuclideanSpace.single (2 : Fin 3) (r / 2)) 2 ≠ 0 := by
    simp [EuclideanSpace.single, hx2, hr.ne']
  exact hy2ne hyA.2

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 4.29 (2): the boundary of that planar closed unit disk is the whole set. -/
theorem boundary_closedUnitDisk_plane_R3_4_29_2 :
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  (∂[@inducedTopology_1_17 (LeanTopology.EuclideanSpaceTopology.E 3) ‹_›]
      {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0})
    = {x : LeanTopology.EuclideanSpaceTopology.E 3 |
        x 0 ^ 2 + x 1 ^ 2 ≤ (1 : ℝ) ∧ x 2 = 0} := by
  letI : DistanceSpace_1_12 (LeanTopology.EuclideanSpaceTopology.E 3) :=
    euclideanDistanceSpace_1_12 3
  rw [boundary_4_27, closure_closedUnitDisk_plane_R3, interior_closedUnitDisk_plane_R3_4_29_2]
  ext x
  simp

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
  have h𝒪 : IsTopology_1_1 X {U : Set X | @IsOpen X T U} :=
    fromMathlibTopologicalSpace_cert T
  refine Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_closure_iff]
    intro U hxU hU
    simpa [Set.inter_comm] using
      (mem_closure_iff_openNeighborhood_4_5 A x).mp hx U
        ⟨⟨U, hxU, hU, Subset.rfl⟩, hxU⟩
  · intro x hx
    refine (mem_closure_iff_openNeighborhood_4_5 A x).mpr ?_
    intro U hU
    rw [mem_closure_iff] at hx
    simpa [Set.inter_comm] using hx U hU.2 ((openNeighborhood_iff_2_2 h𝒪 x U).mp hU).2

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our interior agrees with mathlib's `interior`. -/
theorem interior_eq_mathlibInterior_cert (A : Set X) :
    interior_4_19 {U : Set X | @IsOpen X T U} A = interior A := by
  have h𝒪 : IsTopology_1_1 X {U : Set X | @IsOpen X T U} :=
    fromMathlibTopologicalSpace_cert T
  refine Subset.antisymm ?_ ?_
  · intro x hx
    rcases (mem_interior_iff_openNeighborhood_4_24 A x).mp hx with ⟨V, hV, hVA⟩
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset ((isNeighborhood_iff_mem_nhds_cert T x V).mp hV.1) hVA
  · intro x hx
    exact (mem_interior_iff_isNeighborhood_4_24 A x).2 <|
      (isNeighborhood_iff_mem_nhds_cert T x A).2 (mem_interior_iff_mem_nhds.1 hx)

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our dense subsets agree with mathlib's `Dense`. -/
theorem isDense_iff_mathlibDense_cert (A : Set X) :
    IsDense_4_10 {U : Set X | @IsOpen X T U} A ↔ Dense A := by
  rw [IsDense_4_10, closure_eq_mathlibClosure_cert (T := T) A]
  exact dense_iff_closure_eq.symm

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our boundary agrees with mathlib's `frontier`. -/
theorem boundary_eq_mathlibFrontier_cert (A : Set X) :
    (∂[{U : Set X | @IsOpen X T U}] A) = frontier A := by
  rw [boundary_4_27, closure_eq_mathlibClosure_cert (T := T) A,
    interior_eq_mathlibInterior_cert (T := T) A]
  rfl

end CertifyMathlib

end ClosureInterior
end LeanTopology

/-! 電≠鯨
ぐるぐる夜に、
二人の口ずさむ
歌も掴まれ消えたので
-/
