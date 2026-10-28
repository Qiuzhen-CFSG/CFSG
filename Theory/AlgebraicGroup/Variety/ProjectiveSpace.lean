module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Theory.AlgebraicGroup.Variety.Complete

set_option linter.style.haveILetI false

/-!
# Projective spaces and projective range closures

This module connects the linear-algebraic projectivization used by the Pluecker construction to
the scheme-backed `Variety.Geometric` API.  A finite-dimensional vector space is assigned the
standard `Proj` model with `Fin (Module.finrank k E)` homogeneous coordinates.  The degree-zero
part of its polynomial coordinate ring is identified with `k`; Mathlib's properness theorem for
`Proj` then gives both projectivity and completeness of the resulting geometric variety.

The carrier requires reduced schemes.  Reducedness of projective space is proved stalkwise: each
`Proj` stalk embeds in the ordinary localization of a polynomial ring and is therefore reduced.
An affine homogeneous-coordinate lift is a ring map to global sections whose coordinates avoid
the irrelevant ideal and whose induced `Proj` map lies over `Spec k`.  A convenient constructor
accepts a `k`-algebra map to the presented affine coordinate ring and proves the base compatibility.

Finally, a projective presentation is a closed immersion into finite projective space.  Closed
subvarieties inherit such a presentation and hence completeness.  The scheme-theoretic image of
any geometric morphism is reduced because its affine defining ideals are kernels of maps into
reduced rings; this gives a closed projective range closure whose support is the topological
closure of the morphism's range.  These constructions are the geometric input needed for a
Pluecker orbit closure, without assuming a Borel quotient or a rank-one/PGL2 identification.

The construction follows Hartshorne, *Algebraic Geometry*, II.2 and II.4 (`Proj`, closed
subschemes, and projective properness), and Borovoi, *Linear Algebraic Groups* (`Bor1`), Sections
10-11 and the Pluecker embedding argument for homogeneous spaces.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Variety

universe u

variable {k : Type u} [Field k]

namespace Geometric

/-- The standard graded homogeneous coordinate ring on a finite set of variables. -/
abbrev projectiveCoordinateRing (k : Type u) (sigma : Type) [CommRing k] :=
  MvPolynomial sigma k

/-- The total-degree grading of the standard homogeneous coordinate ring. -/
abbrev projectiveGrading (k : Type u) (sigma : Type) [CommRing k] :=
  MvPolynomial.homogeneousSubmodule sigma k

/-- The canonical graded-algebra structure on the homogeneous coordinate ring.  This instance is
public so exact-import consumers can name the underlying `Proj` without installing Mathlib's
deliberately local `MvPolynomial.gradedAlgebra` instance themselves. -/
instance projectiveGrading_gradedAlgebra (k : Type u) (sigma : Type) [CommRing k] :
    GradedAlgebra (projectiveGrading k sigma) :=
  MvPolynomial.gradedAlgebra

private theorem projectiveGradeZero_bijective {sigma : Type} :
    Function.Bijective (algebraMap k (projectiveGrading k sigma 0)) := by
  constructor
  · intro x y h
    apply FaithfulSMul.algebraMap_injective k (projectiveCoordinateRing k sigma)
    exact congr_arg Subtype.val h
  · rintro ⟨p, hp⟩
    change p ∈ MvPolynomial.homogeneousSubmodule sigma k 0 at hp
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hp
    obtain ⟨r, hr⟩ := hp
    refine ⟨r, Subtype.ext ?_⟩
    change (algebraMap k (projectiveCoordinateRing k sigma)) r = p
    simpa using hr

private instance projectiveGradeZero_isIso {sigma : Type} :
    IsIso (CommRingCat.ofHom (algebraMap k (projectiveGrading k sigma 0))) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr projectiveGradeZero_bijective

private instance projectiveCoordinateRing_finiteType {sigma : Type} [Finite sigma] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule sigma k 0)
      (MvPolynomial sigma k) := by
  rw [← RingHom.finiteType_algebraMap]
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k (MvPolynomial.homogeneousSubmodule sigma k 0))
    (g := algebraMap (MvPolynomial.homogeneousSubmodule sigma k 0) (MvPolynomial sigma k))
  rw [show (algebraMap (MvPolynomial.homogeneousSubmodule sigma k 0)
      (MvPolynomial sigma k)).comp
        (algebraMap k (MvPolynomial.homogeneousSubmodule sigma k 0)) =
      algebraMap k (MvPolynomial sigma k) by
        ext
        rfl]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The standard polynomial `Proj` is reduced over a field. -/
theorem projectiveProj_isReduced {sigma : Type} :
    IsReduced (Proj (projectiveGrading k sigma)) := by
  letI : ∀ x, IsReduced ((Proj (projectiveGrading k sigma)).presheaf.stalk x) := fun x ↦ by
    let I := x.asHomogeneousIdeal.toIdeal
    letI : I.IsPrime := x.isPrime
    letI : IsReduced (Localization I.primeCompl) := by infer_instance
    letI : IsReduced (HomogeneousLocalization.AtPrime (projectiveGrading k sigma) I) :=
      isReduced_of_injective
        (algebraMap (HomogeneousLocalization.AtPrime (projectiveGrading k sigma) I)
          (Localization I.primeCompl))
        (HomogeneousLocalization.val_injective I.primeCompl)
    exact isReduced_of_injective
      (Proj.stalkIso (projectiveGrading k sigma) x).hom.hom
      (Proj.stalkIso (projectiveGrading k sigma) x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk (Proj (projectiveGrading k sigma))

/-- Projective space with homogeneous coordinates indexed by `sigma`. -/
def projectiveSpaceByCoordinates (k : Type u) (sigma : Type) [Field k] [Finite sigma] :
    Geometric k where
  toScheme := Proj (projectiveGrading k sigma)
  structureMap := Proj.toSpecZero (projectiveGrading k sigma) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGrading k sigma 0)))
  finiteType := by infer_instance
  quasiCompact := by infer_instance
  separated := by infer_instance
  reduced := projectiveProj_isReduced

/-- The scheme underlying the coordinate-indexed projective-space carrier is the standard
polynomial `Proj`. -/
@[simp] theorem projectiveSpaceByCoordinates_toScheme (k : Type u) (sigma : Type)
    [Field k] [Finite sigma] :
    (projectiveSpaceByCoordinates k sigma).toScheme = Proj (projectiveGrading k sigma) :=
  rfl

/-- The scheme-backed carrier corresponding to the projectivization `ℙ k E`, using its standard
`Fin (Module.finrank k E)` homogeneous-coordinate model. -/
def projectiveSpace (k E : Type u) [Field k] [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] : Geometric k :=
  projectiveSpaceByCoordinates k (Fin (Module.finrank k E))

/-- The finite-dimensional vector-space carrier uses the standard `Proj` with one coordinate for
each element of `Fin (Module.finrank k E)`. -/
@[simp] theorem projectiveSpace_toScheme (k E : Type u) [Field k] [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] :
    (projectiveSpace k E).toScheme =
      Proj (projectiveGrading k (Fin (Module.finrank k E))) :=
  rfl

/-- The structure morphism of finite projective space is proper. -/
theorem projectiveSpaceByCoordinates_isProper (k : Type u) (sigma : Type)
    [Field k] [Finite sigma] :
    IsProper (projectiveSpaceByCoordinates k sigma).structureMap := by
  change IsProper (Proj.toSpecZero (projectiveGrading k sigma) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGrading k sigma 0))))
  infer_instance

/-- Finite projective space is complete. -/
theorem projectiveSpaceByCoordinates_isComplete (k : Type u) (sigma : Type)
    [Field k] [Finite sigma] : IsComplete (projectiveSpaceByCoordinates k sigma) := by
  letI : IsProper (projectiveSpaceByCoordinates k sigma).structureMap :=
    projectiveSpaceByCoordinates_isProper k sigma
  change UniversallyClosed (projectiveSpaceByCoordinates k sigma).structureMap
  infer_instance

/-- The projective space of a finite-dimensional vector space is complete. -/
theorem projectiveSpace_isComplete (k E : Type u) [Field k] [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] : IsComplete (projectiveSpace k E) := by
  exact projectiveSpaceByCoordinates_isComplete k (Fin (Module.finrank k E))

/-- Homogeneous coordinate data defining an everywhere-regular map from a presented affine
variety to projective space.  The irrelevant-ideal condition says that the coordinates have no
common zero, and `overBase` says that the resulting scheme map is a `k`-morphism. -/
structure AffineHomogeneousCoordinateLift
    (X : Theory.AlgebraicGroup.Variety k) (sigma : Type) [Finite sigma] where
  globalSections : projectiveCoordinateRing k sigma →+* Γ((ofAffine X).toScheme, ⊤)
  irrelevant : Ideal.map globalSections
    (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).toIdeal = ⊤
  overBase :
    Proj.fromOfGlobalSections (projectiveGrading k sigma) globalSections irrelevant ≫
      (projectiveSpaceByCoordinates k sigma).structureMap = (ofAffine X).structureMap

namespace AffineHomogeneousCoordinateLift

/-- Build homogeneous-coordinate data from a `k`-algebra map into the presented affine
coordinate ring. -/
def ofCoordinateRingHom
    {X : Theory.AlgebraicGroup.Variety k} {sigma : Type} [Finite sigma]
    (phi : projectiveCoordinateRing k sigma →ₐ[k] Theory.AlgebraicGroup.coordinateRing X)
    (hphi : Ideal.map
      ((Scheme.ΓSpecIso (.of (Theory.AlgebraicGroup.coordinateRing X))).inv.hom.comp
        phi.toRingHom)
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).toIdeal = ⊤) :
    AffineHomogeneousCoordinateLift X sigma where
  globalSections :=
    (Scheme.ΓSpecIso (.of (Theory.AlgebraicGroup.coordinateRing X))).inv.hom.comp phi.toRingHom
  irrelevant := hphi
  overBase := by
    change Proj.fromOfGlobalSections (projectiveGrading k sigma)
        ((Scheme.ΓSpecIso (.of (Theory.AlgebraicGroup.coordinateRing X))).inv.hom.comp
          phi.toRingHom) hphi ≫
      (Proj.toSpecZero (projectiveGrading k sigma) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGrading k sigma 0)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Theory.AlgebraicGroup.coordinateRing X)))
    rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
      ← SpecMap_ΓSpecIso_hom]
    simp only [← Spec.map_comp, CommRingCat.ofHom_comp]
    congr 1
    ext x
    simp

/-- The scheme map obtained from homogeneous global sections with no common zero. -/
def toSchemeHom {X : Theory.AlgebraicGroup.Variety k} {sigma : Type} [Finite sigma]
    (L : AffineHomogeneousCoordinateLift X sigma) :
    (ofAffine X).toScheme ⟶ (projectiveSpaceByCoordinates k sigma).toScheme :=
  Proj.fromOfGlobalSections (projectiveGrading k sigma) L.globalSections L.irrelevant

/-- The regular map to projective space defined by an affine homogeneous-coordinate lift. -/
def toMorphism {X : Theory.AlgebraicGroup.Variety k} {sigma : Type} [Finite sigma]
    (L : AffineHomogeneousCoordinateLift X sigma) :
    Morphism (ofAffine X) (projectiveSpaceByCoordinates k sigma) where
  hom := L.toSchemeHom
  commutes := L.overBase

end AffineHomogeneousCoordinateLift

/-- A closed immersion into a finite-dimensional projective space. -/
structure ProjectivePresentation (V : Geometric k) where
  Coordinates : Type
  [finiteCoordinates : Finite Coordinates]
  immersion : Morphism V (projectiveSpaceByCoordinates k Coordinates)
  isClosedImmersion : IsClosedImmersion immersion.hom

/-- Projectivity, expressed by a closed immersion into a finite-dimensional projective space. -/
def IsProjective (V : Geometric k) : Prop := Nonempty (ProjectivePresentation V)

/-- Coordinate projective space has its tautological projective presentation. -/
theorem projectiveSpaceByCoordinates_isProjective (k : Type u) (sigma : Type)
    [Field k] [Finite sigma] : IsProjective (projectiveSpaceByCoordinates k sigma) := by
  refine ⟨{ Coordinates := sigma, immersion := Morphism.id _, isClosedImmersion := ?_ }⟩
  simpa using (inferInstance : IsClosedImmersion
    (𝟙 (projectiveSpaceByCoordinates k sigma).toScheme))

/-- The projective space of a finite-dimensional vector space is projective. -/
theorem projectiveSpace_isProjective (k E : Type u) [Field k] [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] : IsProjective (projectiveSpace k E) :=
  projectiveSpaceByCoordinates_isProjective k (Fin (Module.finrank k E))

/-- Every projective geometric variety is complete. -/
theorem IsProjective.isComplete {V : Geometric k} (hV : IsProjective V) : IsComplete V := by
  let P := hV.some
  letI : Finite P.Coordinates := P.finiteCoordinates
  letI : IsClosedImmersion P.immersion.hom := P.isClosedImmersion
  let Z : ClosedSubvariety (projectiveSpaceByCoordinates k P.Coordinates) := {
    toGeometric := V
    inclusion := P.immersion
    isClosedImmersion := P.isClosedImmersion }
  exact Z.isComplete (projectiveSpaceByCoordinates_isComplete k P.Coordinates)

/-- A closed subvariety of a projective variety is projective. -/
theorem ClosedSubvariety.isProjective {V : Geometric k} (Z : ClosedSubvariety V)
    (hV : IsProjective V) : IsProjective Z.toGeometric := by
  let P := hV.some
  letI : Finite P.Coordinates := P.finiteCoordinates
  letI : IsClosedImmersion P.immersion.hom := P.isClosedImmersion
  refine ⟨{
    Coordinates := P.Coordinates
    immersion := Morphism.comp Z.inclusion P.immersion
    isClosedImmersion := ?_ }⟩
  change IsClosedImmersion (Z.inclusion.hom ≫ P.immersion.hom)
  infer_instance

private theorem morphism_quasiCompact {V W : Geometric k} (f : Morphism V W) :
    QuasiCompact f.hom := by
  haveI : QuasiCompact (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact QuasiCompact.of_comp f.hom W.structureMap

/-- The scheme-theoretic image of a morphism from a reduced geometric variety is reduced. -/
theorem schemeTheoreticImage_isReduced {V W : Geometric k} (f : Morphism V W) :
    IsReduced f.hom.image := by
  letI : QuasiCompact f.hom := morphism_quasiCompact f
  exact @IsReduced.of_openCover f.hom.image f.hom.ker.subschemeCover.openCover
      (fun (U : W.toScheme.affineOpens) ↦ by
    letI : IsReduced (Γ(W.toScheme, U.1) ⧸ f.hom.ker.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (by
        rw [Scheme.Hom.ker_apply]
        simpa [RingHom.ker_eq_comap_bot] using
          Ideal.isRadical_bot.comap (f.hom.app U.1).hom)
    change IsReduced (Spec (.of (Γ(W.toScheme, U.1) ⧸ f.hom.ker.ideal U)))
    infer_instance)

namespace Morphism

/-- The reduced scheme-theoretic range closure of a morphism.  Its support is the topological
closure of the point-set range. -/
def schemeTheoreticRangeClosure {V W : Geometric k} (f : Morphism V W) :
    ClosedSubvariety W where
  toGeometric := {
    toScheme := f.hom.image
    structureMap := f.hom.imageι ≫ W.structureMap
    finiteType := by infer_instance
    quasiCompact := by infer_instance
    separated := by infer_instance
    reduced := schemeTheoreticImage_isReduced f }
  inclusion := {
    hom := f.hom.imageι
    commutes := rfl }
  isClosedImmersion := by infer_instance

/-- The canonical factorization through the scheme-theoretic range closure. -/
def toSchemeTheoreticRangeClosure {V W : Geometric k} (f : Morphism V W) :
    Morphism V (f.schemeTheoreticRangeClosure.toGeometric) where
  hom := f.hom.toImage
  commutes := by
    change f.hom.toImage ≫ (f.hom.imageι ≫ W.structureMap) = V.structureMap
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, f.commutes]

@[simp] theorem toSchemeTheoreticRangeClosure_comp_inclusion {V W : Geometric k}
    (f : Morphism V W) :
    (Morphism.comp f.toSchemeTheoreticRangeClosure
      f.schemeTheoreticRangeClosure.inclusion).hom = f.hom :=
  Scheme.Hom.toImage_imageι f.hom

/-- The support of the scheme-theoretic range closure is the topological range closure. -/
theorem range_schemeTheoreticRangeClosure_inclusion {V W : Geometric k}
    (f : Morphism V W) :
    Set.range f.schemeTheoreticRangeClosure.inclusion.hom = closure (Set.range f.hom) := by
  change Set.range f.hom.imageι = closure (Set.range f.hom)
  rw [Scheme.IdealSheafData.range_subschemeι]
  letI : QuasiCompact f.hom := morphism_quasiCompact f
  exact Scheme.Hom.support_ker f.hom

/-- A scheme-theoretic range closure in a projective variety remains projective. -/
theorem schemeTheoreticRangeClosure_isProjective {V W : Geometric k}
    (f : Morphism V W) (hW : IsProjective W) :
    IsProjective f.schemeTheoreticRangeClosure.toGeometric :=
  f.schemeTheoreticRangeClosure.isProjective hW

/-- A scheme-theoretic range closure in a projective variety is complete. -/
theorem schemeTheoreticRangeClosure_isComplete {V W : Geometric k}
    (f : Morphism V W) (hW : IsProjective W) :
    IsComplete f.schemeTheoreticRangeClosure.toGeometric :=
  (f.schemeTheoreticRangeClosure_isProjective hW).isComplete

end Morphism

end Geometric

end Theory.AlgebraicGroup.Variety
