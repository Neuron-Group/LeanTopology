import LeanTopology.RelativeTopology
import Mathlib.CategoryTheory.Category.Basic

/-!
# A small category API for the project topological spaces

This file deliberately does not use mathlib's `TopCat`.  It bundles the
open-set-family topology used throughout the project and equips it with the
standard category structure whose morphisms are the project's continuous maps.
-/

noncomputable section

open Set
open CategoryTheory

namespace LeanTopology
namespace CategoryTopology

open LeanTopology.TopologicalSpace
open LeanTopology.ContinuousMap
open LeanTopology.RelativeTopology

universe u

/-- The project-local category of spaces whose topologies are open-set families. -/
structure TopCat where
  /-- The underlying type of points. -/
  carrier : Type u
  /-- The family of open subsets. -/
  opens : Set (Set carrier)
  /-- The open-set axioms. -/
  isTopology : IsTopology_1_1 carrier opens

namespace TopCat

instance : CoeSort TopCat (Type u) :=
  ⟨TopCat.carrier⟩

attribute [coe] TopCat.carrier

/-- Build a bundled project topological space from an open-set family. -/
def of (X : Type u) (𝒪 : Set (Set X)) (h𝒪 : IsTopology_1_1 X 𝒪) : TopCat :=
  ⟨X, 𝒪, h𝒪⟩

/-- Morphisms are the project's continuous maps. -/
@[ext]
structure Hom (X Y : TopCat.{u}) where
  /-- The underlying function. -/
  toFun : X → Y
  /-- Continuity in the open-set-family sense. -/
  continuous : IsContinuous_5_1 X.opens Y.opens toFun

instance {X Y : TopCat.{u}} : CoeFun (Hom X Y) (fun _ => X → Y) where
  coe f := f.toFun

instance : Category TopCat where
  Hom X Y := Hom X Y
  id X := ⟨id, id_continuous_5_2⟩
  comp f g := ⟨g.toFun ∘ f.toFun, continuous_comp_5_2 f.continuous g.continuous⟩
  id_comp := by
    intro X Y f
    ext x
    rfl
  comp_id := by
    intro X Y f
    ext x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext x
    rfl

instance {X Y : TopCat.{u}} : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := (f : Hom X Y).toFun

@[ext]
theorem hom_ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      congr
      funext x
      exact h x

/-- Construct a morphism from a continuous function. -/
def ofHom {X Y : TopCat.{u}} (f : X → Y) (hf : IsContinuous_5_1 X.opens Y.opens f) :
    X ⟶ Y :=
  ⟨f, hf⟩

@[simp]
theorem id_apply (X : TopCat.{u}) (x : X) : (𝟙 X : X ⟶ X) x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

@[simp]
theorem ofHom_apply {X Y : TopCat.{u}} (f : X → Y)
    (hf : IsContinuous_5_1 X.opens Y.opens f) (x : X) :
    ofHom f hf x = f x :=
  rfl

/-- The project embedding predicate, phrased for morphisms of the local category. -/
def IsEmbedding {X Y : TopCat.{u}} (f : X ⟶ Y) : Prop :=
  IsEmbedding_6_18 X.opens Y.opens f.toFun

namespace IsEmbedding

theorem continuous_toFun {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f) :
    IsContinuous_5_1 X.opens Y.opens f.toFun :=
  hf.continuous

theorem injective_toFun {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f) :
    Function.Injective f.toFun :=
  hf.injective

theorem universalProperty {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (W : TopCat.{u}) (g : W → X)
    (hg : IsContinuous_5_1 W.opens Y.opens (f.toFun ∘ g)) :
    IsContinuous_5_1 W.opens X.opens g :=
  (isEmbedding_iff_universalProperty_6_21
    (𝒪₁ := X.opens) (𝒪₂ := Y.opens) (f := f.toFun)
    f.continuous hf.injective).mp hf W.opens g hg

/-- A raw map whose composite with an embedding is continuous is promoted to a morphism. -/
def liftAlong {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (g : W → X) (hg : IsContinuous_5_1 W.opens Y.opens (f.toFun ∘ g)) : W ⟶ X :=
  ofHom g (hf.universalProperty W g hg)

@[simp]
theorem liftAlong_apply {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (g : W → X) (hg : IsContinuous_5_1 W.opens Y.opens (f.toFun ∘ g)) (w : W) :
    hf.liftAlong g hg w = g w :=
  rfl

@[simp]
theorem liftAlong_comp {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (g : W → X) (hg : IsContinuous_5_1 W.opens Y.opens (f.toFun ∘ g)) :
    hf.liftAlong g hg ≫ f = ofHom (f.toFun ∘ g) hg := by
  ext w
  rfl

/--
If a morphism `h : W ⟶ Y` factors set-theoretically through an embedding `f`,
then the factor is automatically a morphism `W ⟶ X`.
-/
def liftOfFactorization {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (h : W ⟶ Y) (g : W → X) (hfac : ∀ w, h.toFun w = f.toFun (g w)) : W ⟶ X :=
  liftAlong hf g (by
    have hEq : f.toFun ∘ g = h.toFun := by
      funext w
      exact (hfac w).symm
    simpa [hEq] using h.continuous)

@[simp]
theorem liftOfFactorization_apply {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (h : W ⟶ Y) (g : W → X) (hfac : ∀ w, h.toFun w = f.toFun (g w)) (w : W) :
    liftOfFactorization hf h g hfac w = g w :=
  rfl

@[simp]
theorem liftOfFactorization_comp {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (h : W ⟶ Y) (g : W → X) (hfac : ∀ w, h.toFun w = f.toFun (g w)) :
    liftOfFactorization hf h g hfac ≫ f = h := by
  ext w
  exact (hfac w).symm

theorem liftOfFactorization_unique {X Y W : TopCat.{u}} {f : X ⟶ Y} (hf : IsEmbedding f)
    (h : W ⟶ Y) (g : W → X) (hfac : ∀ w, h.toFun w = f.toFun (g w)) {k : W ⟶ X}
    (hk : k ≫ f = h) :
    k = liftOfFactorization hf h g hfac := by
  ext w
  apply hf.injective
  calc
    f (k w) = h w := by
      simpa using congrArg (fun m : W ⟶ Y => m w) hk
    _ = f (g w) := hfac w

theorem existsUnique_liftOfFactorization {X Y W : TopCat.{u}} {f : X ⟶ Y}
    (hf : IsEmbedding f) (h : W ⟶ Y) (g : W → X)
    (hfac : ∀ w, h.toFun w = f.toFun (g w)) :
    ∃! k : W ⟶ X, k ≫ f = h ∧ ∀ w, k w = g w := by
  refine ⟨liftOfFactorization hf h g hfac, ⟨?_, ?_⟩, ?_⟩
  · exact liftOfFactorization_comp hf h g hfac
  · intro w
    rfl
  · intro k hk
    exact liftOfFactorization_unique hf h g hfac hk.1

end IsEmbedding

/--
Categorical form of Proposition 6.21(4): a morphism is an embedding iff it is
injective and every raw map whose composite with it is continuous uniquely
promotes to a morphism into the domain.
-/
theorem isEmbedding_iff_universalProperty {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsEmbedding f <->
      Function.Injective f.toFun ∧
        ∀ (W : TopCat.{u}) (g : W → X),
          IsContinuous_5_1 W.opens Y.opens (f.toFun ∘ g) →
            ∃ k : W ⟶ X, k.toFun = g := by
  constructor
  · intro hf
    refine ⟨hf.injective, ?_⟩
    intro W g hg
    exact ⟨hf.liftAlong g hg, rfl⟩
  · rintro ⟨hfinj, hprop⟩
    let inv : Set.range f.toFun → X := fun y ↦ Classical.choose y.2
    refine ⟨f.continuous, hfinj, ⟨inv, ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · have hrange : MapsTo f.toFun univ (Set.range f.toFun) := by
        intro x _
        exact ⟨x, rfl⟩
      simpa [rangeFactor_6_18, corestrict_6_17] using
        (continuous_corestrict_6_17
          (𝒪₁ := X.opens) (𝒪₂ := Y.opens) f.continuous (Set.range f.toFun) hrange)
    · let R : TopCat.{u} :=
        ⟨Set.range f.toFun, rangeTopology_6_18 Y.opens f.toFun,
          relativeTopology_isTopology_6_1 Y.isTopology (Set.range f.toFun)⟩
      have hcomp : IsContinuous_5_1 R.opens Y.opens (f.toFun ∘ inv) := by
        have hincl :
            IsContinuous_5_1 (rangeTopology_6_18 Y.opens f.toFun) Y.opens
              (inclusionMap_6_2 (Set.range f.toFun)) :=
          inclusion_continuous_6_3 (𝒪 := Y.opens) (A := Set.range f.toFun)
        have hEq : f.toFun ∘ inv = inclusionMap_6_2 (Set.range f.toFun) := by
          funext y
          exact Classical.choose_spec y.2
        simpa [R, hEq] using hincl
      rcases hprop R inv hcomp with ⟨k, hk⟩
      simpa [hk] using k.continuous
    · intro x
      apply hfinj
      exact Classical.choose_spec (rangeFactor_6_18 f.toFun x).2
    · intro y
      apply Subtype.ext
      exact Classical.choose_spec y.2

end TopCat

end CategoryTopology
end LeanTopology
