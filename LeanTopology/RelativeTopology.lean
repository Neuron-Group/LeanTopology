import LeanTopology.ContinuousMap
import LeanTopology.Tactic.TopologyAttr
import Mathlib.Topology.Defs.Induced

/-!
# 拓扑学入门6: 相对拓扑
-/

noncomputable section

open Set

namespace LeanTopology
namespace RelativeTopology

universe u v w

open LeanTopology.TopologicalSpace
open LeanTopology.NeighborhoodBasis
open LeanTopology.Basis
open LeanTopology.ClosureInterior
open LeanTopology.ContinuousMap

section TopologyPart

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {𝒪 : Set (Set X)} {𝒪₁ : Set (Set X)} {𝒪₂ : Set (Set Y)} {𝒪₃ : Set (Set Z)}

/-!
Definition 6.2 introduces the relative topology on a subset. We keep two
parallel interfaces:

* `relativeTopology_6_2 𝒪 A : Set (Set A)` is the intrinsic topology on the subtype;
* `relativeTopologyOn_6_2 𝒪 A : Set (Set X)` is the ambient-language family
  `{U ∩ A | U ∈ 𝒪}`, convenient for statements about subsets of `X`.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 6.2: the intrinsic relative topology on the subtype `A`. -/
def relativeTopology_6_2 (𝒪 : Set (Set X)) (A : Set X) : Set (Set A) :=
  {V : Set A | ∃ U : Set X, U ∈ 𝒪 ∧ V = Subtype.val ⁻¹' U}

/-- The ambient-language family of subsets of `X` that are open in the subspace `A`. -/
def relativeTopologyOn_6_2 (𝒪 : Set (Set X)) (A : Set X) : Set (Set X) :=
  {V : Set X | ∃ U : Set X, U ∈ 𝒪 ∧ V = U ∩ A}

/-- The inclusion map of a subset into its ambient space. -/
abbrev inclusionMap_6_2 (A : Set X) : A -> X := Subtype.val

/-- Restrict an ambient subset to the corresponding subset of the subtype. -/
def subspaceSubset_6_2 (A : Set X) (B : Set X) : Set A :=
  Subtype.val ⁻¹' B

/-- Backward-compatible alias for `subspaceSubset_6_2`. -/
abbrev subspaceSet_6_2 (A : Set X) (B : Set X) : Set A :=
  subspaceSubset_6_2 A B

/-- Restrict a map to a subset of its domain. -/
abbrev restrict_6_4 (f : X → Y) (A : Set X) : A → Y :=
  λ x ↦ f x.1

/-- estricting a map to `A` is composition with inclusion. -/
theorem restrict_eq_comp_inclusion_6_4 {f : X → Y} {A : Set X} :
    restrict_6_4 f A = f ∘ (inclusionMap_6_2 A) :=
  rfl

/-- Corestrict a map to a subset of its codomain. -/
def corestrict_6_17 (f : X → Y) (A : Set Y) (hA : MapsTo f univ A) : X → A :=
  λ x ↦ ⟨f x, hA (mem_univ x)⟩

/-- Factor a map through its range. -/
def rangeFactor_6_18 (f : X → Y) : X → Set.range f :=
  λ x ↦ ⟨f x, ⟨x, rfl⟩⟩

/-- The relative topology on the image/range of a map. -/
abbrev rangeTopology_6_18 (𝒪 : Set (Set Y)) (f : X → Y) : Set (Set (Set.range f)) :=
  relativeTopology_6_2 𝒪 (Set.range f)

/-- The ambient-language family of subsets of `X` that are closed in the subspace `A`. -/
def relativeClosedOn_6_6 (𝒪 : Set (Set X)) (A : Set X) : Set (Set X) :=
  {F : Set X | ∃ C : Set X, IsClosed_1_2 𝒪 C ∧ F = C ∩ A}

/-- The intrinsic family of closed subsets of the subtype `A`. -/
def relativeClosed_6_6 (𝒪 : Set (Set X)) (A : Set X) : Set (Set A) :=
  {F : Set A | ∃ C : Set X, IsClosed_1_2 𝒪 C ∧ F = subspaceSubset_6_2 A C}

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.1: the intrinsic relative topology is a topology. -/
---------------------------------------------------
@[topology]theorem relativeTopology_isTopology_6_1
---------------------------------------------------
(h𝒪 : IsTopology_1_1 X 𝒪)
(A  : Set X             )
---------------------------------------------------
: IsTopology_1_1 A (relativeTopology_6_2 𝒪 A) := by
---------------------------------------------------
refine ⟨?_, ?_, ?_, ?_⟩
· use ∅
  constructor
  · exact h𝒪.O1_empty
  · exact image_val_inj.mp rfl
· use univ
  constructor
  · exact h𝒪.O1_univ
  · exact image_val_inj.mp rfl
· rintro U V
    ⟨U', hU'𝒪, hU'eq⟩
    ⟨V', hV'𝒪, hV'eq⟩
  use U' ∩ V'
  constructor
  · exact h𝒪.O2_inter hU'𝒪 hV'𝒪
  · rw [preimage_inter, ← hU'eq, ← hV'eq]
· intro 𝒮 hyp
  set T : Set (Set X)
    := {W | W ∈ 𝒪 ∧ ∃ U ∈ 𝒮, U = Subtype.val ⁻¹' W}
  use ⋃₀ T
  constructor
  · apply h𝒪.O3_sUnion
    intro U hU
    simp only [↓existsAndEq,
      and_true, mem_setOf_eq, T] at hU
    exact hU.left
  · ext x
    constructor<;>intro hx
    · rcases mem_sUnion.mp hx with ⟨U, hU𝒮, hxU⟩
      rcases hyp U hU𝒮 with ⟨W, hW𝒪, hUeq⟩
      rw [hUeq] at hxU
      exact mem_preimage.mpr
        <| mem_sUnion.mpr
          ⟨W, ⟨hW𝒪, ⟨U, hU𝒮, hUeq⟩⟩, hxU⟩
    · rw [mem_preimage, mem_sUnion] at hx
      rcases hx with ⟨W, hWT, hxW⟩
      rcases hWT.2 with ⟨U, hU𝒮, hUeq⟩
      use U; use hU𝒮; rw [hUeq]
      exact mem_preimage.mpr hxW
---------------------------------------------------

/-- The intrinsic and ambient descriptions of subspace openness agree. -/
---------------------------------------------------
theorem subspaceSubset_mem_relativeTopology_iff_6_2
(A  : Set X )
(U  : Set X )
---------------------------------------------------
: subspaceSubset_6_2 A U ∈ relativeTopology_6_2 𝒪 A
  <-> U ∩ A ∈ relativeTopologyOn_6_2 𝒪 A := by
---------------------------------------------------
constructor <;> intro hyp
· rcases hyp with ⟨V, hVop, hV⟩
  refine ⟨V, hVop, ?_⟩
  ext x
  constructor
  · intro hx
    have hxsub : (⟨x, hx.2⟩ : A) ∈ subspaceSubset_6_2 A U := by
      simpa [subspaceSubset_6_2] using hx.1
    have hxV : (⟨x, hx.2⟩ : A) ∈ Subtype.val ⁻¹' V := by
      simpa [hV] using hxsub
    exact ⟨by simpa using hxV, hx.2⟩
  · intro hx
    have hxV : (⟨x, hx.2⟩ : A) ∈ Subtype.val ⁻¹' V := by
      simpa using hx.1
    have hxsub : (⟨x, hx.2⟩ : A) ∈ subspaceSubset_6_2 A U := by
      simpa [hV] using hxV
    exact ⟨by simpa [subspaceSubset_6_2] using hxsub, hx.2⟩
· rcases hyp with ⟨V, hVop, hV⟩
  refine ⟨V, hVop, ?_⟩
  ext x
  constructor
  · intro hx
    have hxU : x.1 ∈ U := by
      simpa [subspaceSubset_6_2] using hx
    have hxUA : x.1 ∈ U ∩ A := ⟨hxU, x.2⟩
    rw [hV] at hxUA
    simpa using hxUA.1
  · intro hx
    have hxV : x.1 ∈ V := by
      simpa using hx
    have hxVA : x.1 ∈ V ∩ A := ⟨hxV, x.2⟩
    rw [← hV] at hxVA
    simpa [subspaceSubset_6_2] using hxVA.1
---------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.3: the inclusion map is continuous for the relative topology. -/
--------------------------------
theorem inclusion_continuous_6_3
--------------------------------
(A  : Set X )
--------------------------------
: IsContinuous_5_1
  (relativeTopology_6_2 𝒪 A) 𝒪
  (inclusionMap_6_2 A) := by
--------------------------------
intro U Uop
simp only [
  relativeTopology_6_2,
  inclusionMap_6_2,
  mem_setOf_eq
]; use U
--------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.3: the relative topology is the smallest topology
  making the inclusion continuous. -/
-----------------------------------------------------
theorem relativeTopology_minimal_6_3
-----------------------------------------------------
(A      : Set X                                     )
(𝒪A     : Set (Set A)                               )
(hcont  : IsContinuous_5_1 𝒪A 𝒪 (inclusionMap_6_2 A))
-----------------------------------------------------
: relativeTopology_6_2 𝒪 A ⊆ 𝒪A := by
-----------------------------------------------------
intro V hypV
rcases hypV with ⟨U, Uop, hVU⟩
specialize hcont U Uop
unfold inclusionMap_6_2 at hcont
rw [← hVU] at hcont
assumption
-----------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.4: the restriction of a continuous map is continuous. -/
-----------------------------------
theorem continuous_restrict_6_4
-----------------------------------
{f  : X -> Y                  }
(hf : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
(A  : Set X                   )
-----------------------------------
: IsContinuous_5_1
  (relativeTopology_6_2 𝒪₁ A) 𝒪₂
  (restrict_6_4 f A) := by
-----------------------------------
rw [restrict_eq_comp_inclusion_6_4]
have : IsContinuous_5_1
  (relativeTopology_6_2 𝒪₁ A) 𝒪₁
  (inclusionMap_6_2 A)
    := inclusion_continuous_6_3 A
exact continuous_comp_5_2 this hf
-----------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.5: subspace openness is transitive in ambient-language form. -/
-------------------------------------------------------
theorem relativeTopologyOn_transitive_6_5
-------------------------------------------------------
{A B  : Set X }
(hBA  : B ⊆ A )
-------------------------------------------------------
: relativeTopologyOn_6_2 (relativeTopologyOn_6_2 𝒪 A) B
  = relativeTopologyOn_6_2 𝒪 B := by
-------------------------------------------------------
ext W
constructor<;>intro hyp
· rcases hyp with ⟨V, Vop, Weq⟩
  rcases Vop with ⟨U, Uop, Veq⟩
  rw [
    Veq,
    inter_assoc,
    inter_eq_self_of_subset_right hBA,
  ] at Weq
  use U
· rcases hyp with ⟨U, Uop, WUeq⟩
  rw [
    ← inter_eq_self_of_subset_right hBA,
    ← inter_assoc,
  ] at WUeq
  use U ∩ A
  constructor
  · use U
  · assumption
-------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.6: the intrinsic and ambient descriptions of subspace closed sets agree. -/
-------------------------------------------------
theorem subspaceSubset_mem_relativeClosed_iff_6_6
-------------------------------------------------
(A  : Set X )
(F  : Set X )
-------------------------------------------------
: subspaceSubset_6_2 A F ∈ relativeClosed_6_6 𝒪 A
  <-> F ∩ A ∈ relativeClosedOn_6_6 𝒪 A := by
-------------------------------------------------
constructor<;>intro hyp
· rcases hyp with ⟨H, Hcl, Heq⟩
  use H; use Hcl
  ext x; constructor<;>intro xmem
  <;>have := Set.ext_iff.mp Heq
  <;>specialize this ⟨x, xmem.right⟩
  · have := this.mp (by
      simp only [subspaceSubset_6_2,
        mem_preimage]
      exact xmem.left
    )
    exact ⟨this, xmem.right⟩
  · have := this.mpr (by
      simp only [subspaceSubset_6_2,
        mem_preimage]
      exact xmem.left
    )
    exact ⟨this, xmem.right⟩
· rcases hyp with ⟨H, Hcl, Heq⟩
  simp only [
    relativeClosed_6_6, subspaceSubset_6_2,
    mem_setOf_eq
  ]
  use H; use Hcl
  ext x; constructor<;>intro xmem
  <;> have := Set.ext_iff.mp Heq
  · exact this x.val
      |>.mp   ⟨xmem, Subtype.coe_prop x⟩  |>.left
  · exact this x.val
      |>.mpr  ⟨xmem, Subtype.coe_prop x⟩  |>.left
-------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.7: an open subset of an open subspace is open in the ambient space. -/
---------------------------------------
theorem openIn_openIn_ambient_6_7
---------------------------------------
(h𝒪   : IsTopology_1_1 X 𝒪            )
{A B  : Set X                         }
(hA   : A ∈ 𝒪                         )
(hB   : B ∈ relativeTopologyOn_6_2 𝒪 A)
---------------------------------------
: B ∈ 𝒪 := by
---------------------------------------
rcases hB with ⟨U, hU, Beq⟩
exact Beq ▸ h𝒪.O2_inter hU hA
---------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.7: a closed subset of a closed subspace is closed in the ambient space. -/
-------------------------------------
theorem closedIn_closedIn_ambient_6_7
-------------------------------------
(h𝒪   : IsTopology_1_1 X 𝒪          )
{A B  : Set X                       }
(hA   : IsClosed_1_2 𝒪 A            )
(hB   : B ∈ relativeClosedOn_6_6 𝒪 A)
-------------------------------------
: IsClosed_1_2 𝒪 B := by
-------------------------------------
rcases hB with ⟨F, hF, Feq⟩
exact Feq ▸ h𝒪.C3_inter hF hA
-------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.8: an ambient open subset of `A` is open in the subspace `A`. -/
---------------------------------------
theorem open_mem_relativeTopologyOn_6_8
---------------------------------------
{A B  : Set X }
(hBA  : B ⊆ A )
(hB   : B ∈ 𝒪 )
---------------------------------------
: B ∈ relativeTopologyOn_6_2 𝒪 A :=
---------------------------------------
⟨B, ⟨hB, left_eq_inter.mpr hBA⟩⟩
---------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.8: an ambient closed subset of `A` is closed in the subspace `A`. -/
---------------------------------------
theorem closed_mem_relativeClosedOn_6_8
---------------------------------------
{A B  : Set X           }
(hBA  : B ⊆ A           )
(hB   : IsClosed_1_2 𝒪 B)
---------------------------------------
: B ∈ relativeClosedOn_6_6 𝒪 A :=
---------------------------------------
⟨B, ⟨hB, left_eq_inter.mpr hBA⟩⟩
---------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.11: subspaces of first countable spaces are first countable. -/
-----------------------------------------------------------
theorem firstCountable_relativeTopology_6_11
-----------------------------------------------------------
(A  : Set X )
: FirstCountable_2_12 𝒪₁
  -> FirstCountable_2_12
    (relativeTopology_6_2 𝒪₁ A) := by
-----------------------------------------------------------
intro hyp x
topo_auto 𝒪₂ h𝒪₂ for (A : Type u)
  := relativeTopology_6_2 𝒪₁ A
change ∃ 𝒰, IsNeighborhoodBasis_2_5 𝒪₂ x 𝒰
  ∧ 𝒰.Countable
rcases hyp x with ⟨𝒰₁, h𝒰₁, 𝒰₁ctb⟩
rcases h𝒰₁ with ⟨h𝒰₁l, h𝒰₁r⟩
set 𝒰₂ : Set (Set ↑A)
  := {Subtype.val ⁻¹' U | U ∈ 𝒰₁}
use 𝒰₂; refine ⟨⟨?_, ?_⟩, ?_⟩
· intro U₂ hU₂𝒰₂
  simp only [mem_setOf_eq, 𝒰₂] at hU₂𝒰₂
  rcases hU₂𝒰₂ with ⟨U₁, hU₁𝒰₁, hU₁U₂⟩
  specialize h𝒰₁l U₁ hU₁𝒰₁
  rcases h𝒰₁l with ⟨V₁, hV₁𝒪₁, hxV₁, hV₁U₁⟩
  set V₂ : Set ↑A := Subtype.val ⁻¹' V₁
  have hxV₂ : x ∈ V₂
    := mem_preimage.mpr hxV₁
  have hV₂𝒪₂ : V₂ ∈ 𝒪₂ := by
    simp only [relativeTopology_6_2,
      mem_setOf_eq, 𝒪₂]; use V₁
  have hV₂U₂ : V₂ ⊆ U₂ := by
    rw [← hU₁U₂]; dsimp [V₂]
    exact preimage_mono hV₁U₁
  use V₂
· intro V₂ hxV₂
  rcases hxV₂ with ⟨W₂, hW₂𝒪₂, hxW₂, hW₂V₂⟩
  rcases hW₂𝒪₂ with ⟨W₁, hW₁𝒪₁, hW₁W₂⟩
  have hxW₁ : x.1 ∈ W₁ := by
    have : x ∈ Subtype.val ⁻¹' W₁ := by
      simpa [hW₁W₂] using hxW₂
    exact this
  rcases h𝒰₁r W₁ ⟨W₁, hW₁𝒪₁, hxW₁, Subset.rfl⟩
    with ⟨U₁, hU₁𝒰₁, hU₁W₁⟩
  refine ⟨Subtype.val ⁻¹' U₁, ?_, ?_⟩
  · simp only [mem_setOf_eq, 𝒰₂]
    exact ⟨U₁, hU₁𝒰₁, rfl⟩
  · intro y hy
    apply hW₂V₂
    have hy' : y ∈ Subtype.val ⁻¹' W₁ := hU₁W₁ hy
    simpa [hW₁W₂] using hy'
· rw [show 𝒰₂ = (λ U : Set X ↦ Subtype.val ⁻¹' U) '' 𝒰₁ by
      ext U
      constructor
      · intro hU
        simp only [mem_setOf_eq, 𝒰₂] at hU
        rcases hU with ⟨V, hV, rfl⟩
        exact mem_image_of_mem
          (λ U : Set X ↦ Subtype.val ⁻¹' U) hV
      · intro hU
        simp only [mem_image] at hU
        rcases hU with ⟨V, hV, hVU⟩
        exact ⟨V, hV, hVU⟩]
  exact 𝒰₁ctb.image (λ U : Set X ↦ Subtype.val ⁻¹' U)
-----------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.11: subspaces of second countable spaces are second countable. -/
---------------------------------------------------------------------------------
theorem secondCountable_relativeTopology_6_11
---------------------------------------------------------------------------------
(A  : Set X )
---------------------------------------------------------------------------------
: SecondCountable_3_6 𝒪₁ -> SecondCountable_3_6 (relativeTopology_6_2 𝒪₁ A) := by
---------------------------------------------------------------------------------
intro hSecond
rcases hSecond with ⟨ℬ₁, hℬ₁, hℬ₁ctb⟩
let ℬ₂ : Set (Set A) := (fun B : Set X ↦ Subtype.val ⁻¹' B) '' ℬ₁
have hℬ₂ctb : ℬ₂.Countable := hℬ₁ctb.image (fun B : Set X ↦ Subtype.val ⁻¹' B)
refine ⟨ℬ₂, ?_, hℬ₂ctb⟩
constructor
· rintro V ⟨U, hUℬ₁, rfl⟩
  exact ⟨U, hℬ₁.left hUℬ₁, rfl⟩
· intro V hV x hx
  rcases hV with ⟨U, hU𝒪₁, hUV⟩
  have hxU : x.1 ∈ U := by
    have : x ∈ Subtype.val ⁻¹' U := by
      simpa [hUV] using hx
    exact this
  rcases hℬ₁.right U hU𝒪₁ x.1 hxU with ⟨B, hBℬ₁, hxB, hBU⟩
  refine ⟨Subtype.val ⁻¹' B, ?_, ?_, ?_⟩
  · exact mem_image_of_mem (fun B : Set X ↦ Subtype.val ⁻¹' B) hBℬ₁
  · simpa using hxB
  · intro y hy
    have hyU : y.1 ∈ U := hBU hy
    simpa [hUV] using hyU
---------------------------------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.12(1): continuity can be checked on an open cover. -/
-------------------------------------------------------------------------
theorem continuous_of_openCover_6_12
-------------------------------------------------------------------------
{f      : X -> Y                                                        }
(h𝒪₁    : IsTopology_1_1 X 𝒪₁                                           )
(𝒰      : Set (Set X)                                                   )
(hopen  : ∀ U : Set X, U ∈ 𝒰 -> U ∈ 𝒪₁                                  )
(hcover : ⋃₀ 𝒰 = univ                                                   )
(hcont  : ∀ U : Set X, U ∈ 𝒰
  -> IsContinuous_5_1 (relativeTopology_6_2 𝒪₁ U) 𝒪₂ (restrict_6_4 f U) )
-------------------------------------------------------------------------
: IsContinuous_5_1 𝒪₁ 𝒪₂ f := by
-------------------------------------------------------------------------
intro V Vop
have hlocal : ∀ U ∈ 𝒰, (f ⁻¹' V) ∩ U ∈ 𝒪₁ := by
  intro U hU
  have hpre : (restrict_6_4 f U) ⁻¹' V ∈ relativeTopology_6_2 𝒪₁ U := by
    exact hcont U hU V Vop
  have hsub : subspaceSubset_6_2 U (f ⁻¹' V)
    ∈ relativeTopology_6_2 𝒪₁ U := by
      simpa [restrict_6_4, subspaceSubset_6_2] using hpre
  have hrel : (f ⁻¹' V) ∩ U ∈ relativeTopologyOn_6_2 𝒪₁ U := by
    exact subspaceSubset_mem_relativeTopology_iff_6_2
      (𝒪 := 𝒪₁) U (f ⁻¹' V) |>.mp hsub
  exact openIn_openIn_ambient_6_7 h𝒪₁ (hopen U hU) hrel
set 𝒮 : Set (Set X) := {W : Set X | ∃ U ∈ 𝒰, W = (f ⁻¹' V) ∩ U}
have h𝒮open : ∀ W ∈ 𝒮, W ∈ 𝒪₁ := by
  intro W hW
  simp only [mem_setOf_eq, 𝒮] at hW
  rcases hW with ⟨U, hU, rfl⟩
  exact hlocal U hU
have hEq : ⋃₀ 𝒮 = f ⁻¹' V := by
  ext x
  constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨W, hW𝒮, hxW⟩
    simp only [mem_setOf_eq, 𝒮] at hW𝒮
    rcases hW𝒮 with ⟨U, hU, rfl⟩
    exact hxW.1
  · intro hx
    have hxcover : x ∈ ⋃₀ 𝒰 := by
      rw [hcover]
      exact mem_univ x
    rcases mem_sUnion.mp hxcover with ⟨U, hU, hxU⟩
    apply mem_sUnion.mpr
    refine ⟨(f ⁻¹' V) ∩ U, ?_, ⟨hx, hxU⟩⟩
    simp only [mem_setOf_eq, 𝒮]
    exact ⟨U, hU, rfl⟩
rw [← hEq]
exact h𝒪₁.O3_sUnion 𝒮 h𝒮open
-------------------------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.12(2): continuity can be checked on a finite closed cover. -/
-------------------------------------------------------------------------
theorem continuous_of_finiteClosedCover_6_12
-------------------------------------------------------------------------
{f        : X -> Y                                                      }
(h𝒪₁      : IsTopology_1_1 X 𝒪₁                                         )
(ℱ        : Finset (Set X)                                              )
(hclosed  : ∀ F : Set X, F ∈ ℱ -> IsClosed_1_2 𝒪₁ F                     )
(hcover   : ⋃₀ (↑ℱ : Set (Set X)) = univ                                )
(hcont    : ∀ F : Set X, F ∈ ℱ
  -> IsContinuous_5_1 (relativeTopology_6_2 𝒪₁ F) 𝒪₂ (restrict_6_4 f F) )
-------------------------------------------------------------------------
: IsContinuous_5_1 𝒪₁ 𝒪₂ f := by
-------------------------------------------------------------------------
apply (continuous_iff_preimage_closed_5_4 (𝒪₁ := 𝒪₁) (𝒪₂ := 𝒪₂) f).mpr
intro H hHcl
have hlocal : ∀ F ∈ ℱ, IsClosed_1_2 𝒪₁ ((f ⁻¹' H) ∩ F) := by
  intro F hF
  have hpre : IsClosed_1_2
    (relativeTopology_6_2 𝒪₁ F) ((restrict_6_4 f F) ⁻¹' H) := by
      exact continuous_iff_preimage_closed_5_4
        (𝒪₁ := relativeTopology_6_2 𝒪₁ F) (𝒪₂ := 𝒪₂) (restrict_6_4 f F)
          |>.mp (hcont F hF) H hHcl
  have hsub : IsClosed_1_2
    (relativeTopology_6_2 𝒪₁ F) (subspaceSubset_6_2 F (f ⁻¹' H)) := by
      simpa [restrict_6_4, subspaceSubset_6_2] using hpre
  have hsub' : subspaceSubset_6_2 F (f ⁻¹' H)
    ∈ relativeClosed_6_6 𝒪₁ F := by
      rcases hsub with ⟨U, hU, hEq⟩
      refine ⟨Uᶜ, closed_of_open_compl hU, ?_⟩
      calc
        subspaceSubset_6_2 F (f ⁻¹' H)
          = ((subspaceSubset_6_2 F (f ⁻¹' H))ᶜ)ᶜ := by
            simp only [compl_compl]
        _ = (Subtype.val ⁻¹' U)ᶜ := by rw [hEq]
        _ = Subtype.val ⁻¹' Uᶜ := by simp [preimage_compl]
  have hrel : (f ⁻¹' H) ∩ F ∈ relativeClosedOn_6_6 𝒪₁ F := by
    exact subspaceSubset_mem_relativeClosed_iff_6_6
      (𝒪 := 𝒪₁) F (f ⁻¹' H) |>.mp hsub'
  exact closedIn_closedIn_ambient_6_7 h𝒪₁ (hclosed F hF) hrel
set 𝒮 : Finset (Set X)
  := ℱ.attach.image (λ F : {F // F ∈ ℱ} ↦ (f ⁻¹' H) ∩ F.1)
have h𝒮closed : ∀ S ∈ 𝒮, IsClosed_1_2 𝒪₁ S := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨F, hF, rfl⟩
  exact hlocal F.1 F.2
have hEq : ⋃₀ (↑𝒮 : Set (Set X)) = f ⁻¹' H := by
  ext x
  constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨S, hS𝒮, hxS⟩
    rcases Finset.mem_image.mp hS𝒮 with ⟨F, hF, hFS⟩
    rw [← hFS] at hxS
    exact hxS.1
  · intro hx
    have hxcover : x ∈ ⋃₀ (↑ℱ : Set (Set X)) := by
      rw [hcover]
      exact mem_univ x
    rcases mem_sUnion.mp hxcover with ⟨F, hF, hxF⟩
    apply mem_sUnion.mpr
    refine ⟨(f ⁻¹' H) ∩ F, ?_, ⟨hx, hxF⟩⟩
    change (f ⁻¹' H) ∩ F ∈ 𝒮
    exact Finset.mem_image.mpr ⟨⟨F, hF⟩, by simp, rfl⟩
have hClosedFam : IsClosedFamily_1_3 X {F : Set X | IsClosed_1_2 𝒪₁ F}
  := closedSet_properties_1_3.mp h𝒪₁
rw [← hEq]
exact hClosedFam.C2_union' 𝒮 h𝒮closed
-------------------------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.14: convergence in a subspace agrees with ambient convergence. -/
-----------------------------------------------------
theorem tendstoSeq_relativeTopology_iff_6_14
-----------------------------------------------------
(A  : Set X           )
(xₙ : Sequence_2_16 A )
(x  : A               )
-----------------------------------------------------
: TendstoSeq_2_16 (relativeTopology_6_2 𝒪 A) xₙ x
  <-> TendstoSeq_2_16 𝒪 (λ n ↦ (xₙ n).1) x.1 := by
-----------------------------------------------------
constructor<;>intro hyp V hV
· have hVsub : IsNeighborhood_2_1
    (relativeTopology_6_2 𝒪 A)
    x (Subtype.val ⁻¹' V) := by
      rcases hV with ⟨U, hU𝒪, hxU, hUV⟩
      refine ⟨Subtype.val ⁻¹' U, ?_, ?_, ?_⟩
      · exact ⟨U, hU𝒪, rfl⟩
      · simpa using hxU
      · exact preimage_mono hUV
  rcases hyp (Subtype.val ⁻¹' V) hVsub with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn
· rcases hV with ⟨W, hWrel, hxW, hWV⟩
  rcases hWrel with ⟨U, hU𝒪, hWU⟩
  have hxU : x.1 ∈ U := by
    have : x ∈ Subtype.val ⁻¹' U := by
      simpa [hWU] using hxW
    exact this
  rcases hyp U ⟨U, hU𝒪, hxU, Subset.rfl⟩ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hxUn : (xₙ n).1 ∈ U := hN n hn
  have hxWn : xₙ n ∈ W := by
    have : xₙ n ∈ Subtype.val ⁻¹' U := hxUn
    simpa [hWU] using this
  exact hWV hxWn
-----------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.15: closure in a subspace is the ambient closure intersected with the subspace. -/
/- ----------------------------------------------------------------------------
  One subtle here: If B ⊄ A, we should not immediately say Cl_A B = A ∩ B̄
  Instance : Put A = {0} and B = {1 / n | n ∈ ℕ⁺}
    We got A ∩ B̄ = 0, but since A ∩ B = ∅, Cl_A B = ∅.
------------------------------------------------------------------------------/
-------------------------------------------------------------------------------
theorem closure_relativeTopology_6_15
-------------------------------------------------------------------------------
(A B  : Set X )
(hBA  : B ⊆ A )
-------------------------------------------------------------------------------
: closure_4_1 (relativeTopology_6_2 𝒪 A) (subspaceSubset_6_2 A B)
  = subspaceSubset_6_2 A (A ∩ closure_4_1 𝒪 B) := by
-------------------------------------------------------------------------------
ext x; constructor<;>intro hyp
· have hxcl : x.1 ∈ closure_4_1 𝒪 B := by
    apply mem_closure_iff_openNeighborhood_4_5 B x.1 |>.mpr
    rintro U ⟨hUx, hU⟩
    have hUsub : subspaceSubset_6_2 A U ∈ relativeTopology_6_2 𝒪 A := by
      exact ⟨U, hU, rfl⟩
    have hxUsub : x ∈ subspaceSubset_6_2 A U := by
      rcases hUx with ⟨W, hW, hxW, hWU⟩
      exact hWU hxW
    have hnonempty :=
      (mem_closure_iff_openNeighborhood_4_5 (subspaceSubset_6_2 A B) x).mp hyp
        (subspaceSubset_6_2 A U) ⟨neighborhood_of_open_mem hUsub hxUsub, hUsub⟩
    rcases hnonempty with ⟨y, hyB, hyU⟩
    refine ⟨y.1, ?_, ?_⟩
    · simpa [subspaceSubset_6_2] using hyB
    · simpa [subspaceSubset_6_2] using hyU
  simpa [subspaceSubset_6_2] using
    (show x.1 ∈ A ∩ closure_4_1 𝒪 B from ⟨x.2, hxcl⟩)
· apply mem_closure_iff_openNeighborhood_4_5
    (subspaceSubset_6_2 A B) x |>.mpr
  rintro V ⟨hV, VopA⟩
  rcases VopA with ⟨U, Uop, hVU⟩
  have hxV : x ∈ V := by
    rcases hV with ⟨W, hW, hxW, hWV⟩
    exact hWV hxW
  have hxU : x.1 ∈ U := by
    simpa [hVU] using hxV
  have hxcl : x.1 ∈ closure_4_1 𝒪 B := by
    exact hyp.2
  have hnonempty :=
    (mem_closure_iff_openNeighborhood_4_5 B x.1).mp hxcl U
      ⟨neighborhood_of_open_mem Uop hxU, Uop⟩
  rcases hnonempty with ⟨y, hyB, hyU⟩
  refine ⟨⟨y, hBA hyB⟩, ?_, ?_⟩
  · simpa [subspaceSubset_6_2] using hyB
  · have hyV : (⟨y, hBA hyB⟩ : A) ∈ V := by
      have : (⟨y, hBA hyB⟩ : A) ∈ Subtype.val ⁻¹' U := by
        exact hyU
      simpa [hVU] using this
    exact hyV
-------------------------------------------------------------------------------

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.17: corestricting a continuous map to a subspace preserves continuity. -/
------------------------------------------------------------
theorem continuous_corestrict_6_17
------------------------------------------------------------
{f  : X -> Y                  }
(hf : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
(A  : Set Y                   )
(hA : MapsTo f univ A         )
------------------------------------------------------------
: IsContinuous_5_1 𝒪₁
  (relativeTopology_6_2 𝒪₂ A) (corestrict_6_17 f A hA) := by
------------------------------------------------------------
set fₐ  : X -> A := corestrict_6_17 f A hA
set i   : A -> Y := inclusionMap_6_2 A
have feq : f = i ∘ fₐ := by
  funext x
  rfl
intro V VopA
simp only [relativeTopology_6_2, mem_setOf_eq] at VopA
rcases VopA with ⟨U, Uop, hVU⟩
change V = i ⁻¹' U at hVU
rw [hVU]
change (i ∘ fₐ) ⁻¹' U  ∈ 𝒪₁
rw [← feq]
exact hf U Uop
------------------------------------------------------------

section EmbeddingPart

open LeanTopology.ContinuousMap

private abbrev RelativeHomeomorphism_6_18
    (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) (f : X → Y) :=
  LeanTopology.ContinuousMap.IsHomeomorphism_5_20 𝒪₁ (rangeTopology_6_18 𝒪₂ f)

/-!
Definition 6.18 introduces embeddings. We phrase it using the factorization of
`f` through its range equipped with the relative topology inherited from the
codomain.
-/

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 6.18: a topological embedding is a continuous injective map whose range factor is a homeomorphism. -/
def IsEmbedding_6_18 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) (f : X → Y) : Prop :=
  IsContinuous_5_1 𝒪₁ 𝒪₂ f ∧
    Function.Injective f ∧
      ∃ h : RelativeHomeomorphism_6_18 𝒪₁ 𝒪₂ f,
        h.toFun = rangeFactor_6_18 f

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.21(2): for a continuous injective map,
being an embedding is equivalent to openness of images in the subspace range. -/
theorem isEmbedding_iff_imageOpenInRange_6_21 {f : X → Y}
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hfinj : Function.Injective f) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f
      <->
        ∀ U : Set X, U ∈ 𝒪₁ -> f '' U ∈ relativeTopologyOn_6_2 𝒪₂ (Set.range f) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.21(3): for a continuous injective map,
being an embedding is equivalent to closedness of images in the subspace range. -/
theorem isEmbedding_iff_imageClosedInRange_6_21 {f : X → Y}
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hfinj : Function.Injective f) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f
      <->
        ∀ F : Set X, IsClosed_1_2 𝒪₁ F -> f '' F ∈ relativeClosedOn_6_6 𝒪₂ (Set.range f) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.21(4): for a continuous injective map,
being an embedding is equivalent to the universal property against continuity. -/
theorem isEmbedding_iff_universalProperty_6_21 {f : X → Y}
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hfinj : Function.Injective f) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f
      <->
        ∀ {W : Type w} (𝒪W : Set (Set W)) (g : W → X),
          IsContinuous_5_1 𝒪W 𝒪₂ (f ∘ g) -> IsContinuous_5_1 𝒪W 𝒪₁ g := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.22(1): the composition of embeddings is an embedding. -/
theorem embedding_comp_6_22 {f : X → Y} {g : Y → Z}
    (hf : IsEmbedding_6_18 𝒪₁ 𝒪₂ f)
    (hg : IsEmbedding_6_18 𝒪₂ 𝒪₃ g) :
    IsEmbedding_6_18 𝒪₁ 𝒪₃ (g ∘ f) := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.22(2): if a composite is an embedding, then the first map is an embedding. -/
theorem embedding_of_comp_6_22 {f : X → Y} {g : Y → Z}
    (hgf : IsEmbedding_6_18 𝒪₁ 𝒪₃ (g ∘ f))
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hgcont : IsContinuous_5_1 𝒪₂ 𝒪₃ g) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.23: a continuous injective open map is an embedding. -/
theorem embedding_of_openMap_6_23 {f : X → Y}
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hfinj : Function.Injective f)
    (hfopen : IsOpenMap_5_26 𝒪₁ 𝒪₂ f) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.23: a continuous injective closed map is an embedding. -/
theorem embedding_of_closedMap_6_23 {f : X → Y}
    (hfcont : IsContinuous_5_1 𝒪₁ 𝒪₂ f)
    (hfinj : Function.Injective f)
    (hfclosed : IsClosedMap_5_26 𝒪₁ 𝒪₂ f) :
    IsEmbedding_6_18 𝒪₁ 𝒪₂ f := by
  sorry

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 6.24: an open embedding is an embedding that is also an open map. -/
def IsOpenEmbedding_6_24 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) (f : X → Y) : Prop :=
  IsEmbedding_6_18 𝒪₁ 𝒪₂ f ∧ IsOpenMap_5_26 𝒪₁ 𝒪₂ f

/-- 𝒟ℯ𝒻𝒾𝓃𝒾𝓉𝒾ℴ𝓃 6.24: a closed embedding is an embedding that is also a closed map. -/
def IsClosedEmbedding_6_24 (𝒪₁ : Set (Set X)) (𝒪₂ : Set (Set Y)) (f : X → Y) : Prop :=
  IsEmbedding_6_18 𝒪₁ 𝒪₂ f ∧ IsClosedMap_5_26 𝒪₁ 𝒪₂ f

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.25: for an embedding, being an open embedding is equivalent to having open range. -/
theorem isOpenEmbedding_iff_open_range_6_25 {f : X → Y}
    (hf : IsEmbedding_6_18 𝒪₁ 𝒪₂ f) :
    IsOpenEmbedding_6_24 𝒪₁ 𝒪₂ f <-> Set.range f ∈ 𝒪₂ := by
  sorry

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.25: for an embedding, being a closed embedding is equivalent to having closed range. -/
theorem isClosedEmbedding_iff_closed_range_6_25 {f : X → Y}
    (hf : IsEmbedding_6_18 𝒪₁ 𝒪₂ f) :
    IsClosedEmbedding_6_24 𝒪₁ 𝒪₂ f <-> IsClosed_1_2 𝒪₂ (Set.range f) := by
  sorry

end EmbeddingPart

end TopologyPart

section MetricPart

variable {X : Type u}
variable [DistanceSpace_1_12 X]

open LeanTopology.TopologicalSpace.DistanceSpace_1_12

/-- 𝒫𝓇ℴ𝓅ℴ𝓈𝒾𝓉𝒾ℴ𝓃 6.9: the relative topology of a metric subspace agrees with the topology induced by the restricted distance. -/
--------------------------------------------------------
theorem relativeTopology_eq_restrictDistanceTopology_6_9
--------------------------------------------------------
(A  : Set X )
--------------------------------------------------------
: relativeTopology_6_2 (
    @inducedTopology_1_17
      X ‹DistanceSpace_1_12 X›
  ) A
  = @inducedTopology_1_17 A (
      restrictDistance_1_13 (
        D := ‹DistanceSpace_1_12 X›
      ) A
    ) := by
--------------------------------------------------------
topo_auto 𝒪 h𝒪 for X := @inducedTopology_1_17 X _

letI : DistanceSpace_1_12 (A : Type u) :=
  restrictDistance_1_13 (D := ‹DistanceSpace_1_12 X›) A
topo_auto 𝒪ₐ h𝒪ₐ for (A : Type u) :=
  @inducedTopology_1_17 (A : Type u) inferInstance

change relativeTopology_6_2 𝒪 A = 𝒪ₐ

ext V
constructor <;> intro hyp
· change isOpenDistance_1_15 V
  rcases hyp with ⟨U, Uop, rfl⟩
  intro x' hxV
  rcases x' with ⟨x, hxA⟩
  have hxU : x ∈ U := by
    simpa using hxV
  simp only [𝒪, inducedTopology_1_17,
    isOpenDistance_1_15, mem_setOf_eq] at Uop
  rcases Uop x hxU with ⟨r, rpos, hball⟩
  refine ⟨r, rpos, ?_⟩
  intro y' hy'
  rcases y' with ⟨y, hyA⟩
  have hyU : y ∈ U
    := hball (by simpa [openBall_1_14] using hy')
  simpa using hyU
· change isOpenDistance_1_15 V at hyp
  let 𝒮 : Set (Set A) :=
    {W | ∃ x ∈ V, ∃ r > 0,
      W = openBall_1_14 x r ∧ W ⊆ V}
  have hSopen
    : ∀ W ∈ 𝒮, W ∈ relativeTopology_6_2 𝒪 A := by
    intro W hW
    rcases hW with ⟨x, hxV, r, rpos, rfl, hWV⟩
    refine ⟨openBall_1_14 x.1 r, ?_, ?_⟩
    · simpa [𝒪, inducedTopology_1_17, mem_setOf_eq]
        using openBall_open_1_16 x.1 r
    · ext y
      rfl
  have hrel
    :   IsTopology_1_1 A (relativeTopology_6_2 𝒪 A)
    :=  relativeTopology_isTopology_6_1 h𝒪 A
  have hsUnion : ⋃₀ 𝒮 ∈ relativeTopology_6_2 𝒪 A
    := hrel.O3_sUnion 𝒮 hSopen
  have hVeq : ⋃₀ 𝒮 = V := by
    ext y
    constructor
    · intro hy
      rcases mem_sUnion.mp hy with ⟨W, hW𝒮, hyW⟩
      rcases hW𝒮 with ⟨x, hxV, r, rpos, hW, hWV⟩
      exact hWV (by simpa [hW] using hyW)
    · intro hyV
      rcases hyp y hyV with ⟨r, rpos, hball⟩
      refine mem_sUnion.mpr ?_
      refine ⟨openBall_1_14 y r, ?_, ?_⟩
      · exact ⟨y, hyV, r, rpos, rfl, hball⟩
      · have hyy : dist y y = 0
          := DistanceSpace_1_12.D1 y y |>.2 rfl
        simpa [openBall_1_14, hyy] using rpos
  simpa [hVeq] using hsUnion
--------------------------------------------------------

end MetricPart

open Topology

section CertifyMathlib

variable {X : Type u} {Y : Type v}
variable (T : TopologicalSpace X) (T₁ : TopologicalSpace X) (T₂ : TopologicalSpace Y)

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our relative topology agrees with mathlib's induced subtype topology. -/
theorem relativeTopology_iff_mathlibSubspace_cert (A : Set X) :
    relativeTopology_6_2 {U : Set X | @IsOpen X T U} A
      =
        {V : Set A | @IsOpen A (TopologicalSpace.induced Subtype.val T) V} := by
  sorry

/-- 𝒱ℯ𝓇𝒾𝒻𝒾𝒸𝒶𝓉𝒾ℴ𝓃 : our embedding notion agrees with mathlib's `Topology.IsEmbedding`. -/
theorem isEmbedding_iff_mathlibIsEmbedding_cert (f : X → Y) :
    IsEmbedding_6_18
      {U : Set X | @IsOpen X T₁ U}
      {V : Set Y | @IsOpen Y T₂ V} f
        <-> Topology.IsEmbedding f := by
  sorry

end CertifyMathlib

section Example613

open LeanTopology.TopologicalSpace
open LeanTopology.ContinuousMap

variable {Y : Type v} (T : TopologicalSpace Y)

/-- The closed unit interval `[0,1]` used in Example 6.13. -/
abbrev UnitInterval_6_13 := Set.Icc (0 : ℝ) 1

/-- The relative topology on `[0,1]` inherited from `ℝ`. -/
abbrev unitIntervalTopology_6_13 : Set (Set UnitInterval_6_13) :=
  relativeTopology_6_2 {U : Set ℝ | @IsOpen ℝ inferInstance U} UnitInterval_6_13

/-- The left half `[0, 1/2]` of the unit interval. -/
abbrev leftHalfSet_6_13 : Set UnitInterval_6_13 :=
  {t | t.1 ≤ (1 : ℝ) / 2}

/-- The right half `[1/2, 1]` of the unit interval. -/
abbrev rightHalfSet_6_13 : Set UnitInterval_6_13 :=
  {t | (1 : ℝ) / 2 ≤ t.1}

/-- Reparameterize the left half `[0,1/2]` onto `[0,1]` by `t ↦ 2t`. -/
abbrev leftReparam_6_13 (t : leftHalfSet_6_13.Elem) : UnitInterval_6_13 := by
  refine ⟨2 * t.1.1, ?_⟩
  constructor
  · nlinarith [t.1.2.1]
  · have ht : t.1.1 ≤ (1 : ℝ) / 2 := by
      simpa [leftHalfSet_6_13] using t.2
    nlinarith

/-- Reparameterize the right half `[1/2,1]` onto `[0,1]` by `t ↦ 2t - 1`. -/
abbrev rightReparam_6_13 (t : rightHalfSet_6_13.Elem) : UnitInterval_6_13 := by
  refine ⟨2 * t.1.1 - 1, ?_⟩
  constructor
  · have ht : (1 : ℝ) / 2 ≤ t.1.1 := by
      simpa [rightHalfSet_6_13] using t.2
    nlinarith
  · nlinarith [t.1.2.2]

/-- The left endpoint `0 ∈ [0,1]`. -/
abbrev zeroUnit_6_13 : UnitInterval_6_13 :=
  ⟨0, by simp [UnitInterval_6_13]⟩

/-- The right endpoint `1 ∈ [0,1]`. -/
abbrev oneUnit_6_13 : UnitInterval_6_13 :=
  ⟨1, by simp [UnitInterval_6_13]⟩

/-- Example 6.13: concatenate two maps on `[0,1]` by traversing the first on
`[0,1/2]` and the second on `[1/2,1]`. -/
def pathConcat_6_13 (f g : UnitInterval_6_13 → Y) :
    UnitInterval_6_13 → Y :=
  λ t ↦
    if ht : t.1 ≤ (1 : ℝ) / 2 then
      f ⟨2 * t.1, by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [t.2.2, ht]⟩
    else
      g ⟨2 * t.1 - 1, by
        constructor
        · nlinarith [t.2.1, ht]
        · nlinarith [t.2.2]⟩

/-- ℰ𝓍𝒶𝓂𝓅𝓁ℯ 6.13: concatenating two continuous paths with matching endpoints
gives a continuous path on `[0,1]`.

We place the formalization here because the proof uses the certification that
our relative topology matches mathlib's subtype topology. -/
theorem pathConcat_continuous_6_13
    {f g : UnitInterval_6_13 → Y}
    (hf : IsContinuous_5_1 (unitIntervalTopology_6_13)
      {V : Set Y | @IsOpen Y T V} f)
    (hg : IsContinuous_5_1 (unitIntervalTopology_6_13)
      {V : Set Y | @IsOpen Y T V} g)
    (hfg : f (oneUnit_6_13) = g (zeroUnit_6_13)) :
    IsContinuous_5_1 (unitIntervalTopology_6_13)
      {V : Set Y | @IsOpen Y T V}
      (pathConcat_6_13 f g) := by
  have hI : IsTopology_1_1 UnitInterval_6_13 (unitIntervalTopology_6_13) := by
    exact relativeTopology_isTopology_6_1
      (X := ℝ) (𝒪 := {U : Set ℝ | IsOpen U})
      (fromMathlibTopologicalSpace_cert inferInstance) UnitInterval_6_13
  have hIcert : unitIntervalTopology_6_13 = {V : Set UnitInterval_6_13 | IsOpen V} := by
    exact relativeTopology_iff_mathlibSubspace_cert (T := inferInstance) UnitInterval_6_13
  have hleftCont_mathlib :
      Continuous (leftReparam_6_13 : leftHalfSet_6_13.Elem → UnitInterval_6_13) := by
    exact Continuous.subtype_mk (by continuity) (by
      intro t
      constructor
      · nlinarith [t.1.2.1]
      · have ht : t.1.1 ≤ (1 : ℝ) / 2 := by
          simpa [leftHalfSet_6_13] using t.2
        nlinarith)
  have hrightCont_mathlib :
      Continuous (rightReparam_6_13 : rightHalfSet_6_13.Elem → UnitInterval_6_13) := by
    exact Continuous.subtype_mk (by continuity) (by
      intro t
      constructor
      · have ht : (1 : ℝ) / 2 ≤ t.1.1 := by
          simpa [rightHalfSet_6_13] using t.2
        nlinarith
      · nlinarith [t.1.2.2])
  have hleftCont : IsContinuous_5_1
      (relativeTopology_6_2 (unitIntervalTopology_6_13) leftHalfSet_6_13)
      (unitIntervalTopology_6_13) leftReparam_6_13 := by
    rw [hIcert]
    rw [relativeTopology_iff_mathlibSubspace_cert (X := UnitInterval_6_13)
      (T := inferInstance) leftHalfSet_6_13]
    exact (isContinuous_iff_mathlibContinuous_cert
      (T₁ := TopologicalSpace.induced Subtype.val inferInstance)
      (T₂ := inferInstance) leftReparam_6_13).mpr hleftCont_mathlib
  have hrightCont : IsContinuous_5_1
      (relativeTopology_6_2 (unitIntervalTopology_6_13) rightHalfSet_6_13)
      (unitIntervalTopology_6_13) rightReparam_6_13 := by
    rw [hIcert]
    rw [relativeTopology_iff_mathlibSubspace_cert (X := UnitInterval_6_13)
      (T := inferInstance) rightHalfSet_6_13]
    exact (isContinuous_iff_mathlibContinuous_cert
      (T₁ := TopologicalSpace.induced Subtype.val inferInstance)
      (T₂ := inferInstance) rightReparam_6_13).mpr hrightCont_mathlib
  have hleftClosedMathlib : IsClosed (leftHalfSet_6_13 : Set UnitInterval_6_13) := by
    simpa [leftHalfSet_6_13] using
      (isClosed_le continuous_subtype_val continuous_const :
        IsClosed {t : UnitInterval_6_13 | t.1 ≤ (1 : ℝ) / 2})
  have hrightClosedMathlib : IsClosed (rightHalfSet_6_13 : Set UnitInterval_6_13) := by
    simpa [rightHalfSet_6_13] using
      (isClosed_le continuous_const continuous_subtype_val :
        IsClosed {t : UnitInterval_6_13 | (1 : ℝ) / 2 ≤ t.1})
  refine continuous_of_finiteClosedCover_6_12 (𝒪₁ := unitIntervalTopology_6_13)
    (𝒪₂ := {V : Set Y | @IsOpen Y T V}) hI
      ({leftHalfSet_6_13, rightHalfSet_6_13} : Finset (Set UnitInterval_6_13)) ?_ ?_ ?_
  · intro F hF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF
    rcases hF with rfl | rfl
    · rw [hIcert, IsClosed_1_2]
      exact hleftClosedMathlib.isOpen_compl
    · rw [hIcert, IsClosed_1_2]
      exact hrightClosedMathlib.isOpen_compl
  · ext t
    simp only [
      leftHalfSet_6_13, one_div, rightHalfSet_6_13, Finset.coe_insert,
      Finset.coe_singleton, sUnion_insert, sUnion_singleton, mem_union,
      mem_setOf_eq, mem_univ, iff_true
    ]
    exact le_total t.1 ((2 : ℝ)⁻¹)
  · intro F hF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF
    rcases hF with rfl | rfl
    · have hEq :
        restrict_6_4 (pathConcat_6_13 f g) leftHalfSet_6_13
          = f ∘ leftReparam_6_13 := by
          funext t
          have ht : t.1.1 ≤ (2 : ℝ)⁻¹ := by
            simpa [leftHalfSet_6_13] using t.2
          simp [pathConcat_6_13, leftReparam_6_13, ht]
      rw [hEq]
      exact continuous_comp_5_2 hleftCont hf
    · have hEq :
        restrict_6_4 (pathConcat_6_13 f g) rightHalfSet_6_13
          = g ∘ rightReparam_6_13 := by
          funext t
          by_cases ht : t.1.1 ≤ (2 : ℝ)⁻¹
          · have htr : (2 : ℝ)⁻¹ ≤ t.1.1 := by
              simpa [rightHalfSet_6_13] using t.2
            have hhalf : t.1.1 = (2 : ℝ)⁻¹ := by
              nlinarith
            simpa [pathConcat_6_13, rightReparam_6_13, hhalf,
              oneUnit_6_13, zeroUnit_6_13] using hfg
          · simp [pathConcat_6_13, rightReparam_6_13, ht]
      rw [hEq]
      exact continuous_comp_5_2 hrightCont hg

end Example613

end RelativeTopology
end LeanTopology
