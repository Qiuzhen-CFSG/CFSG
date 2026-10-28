module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Theory.AlgebraicGroup.Variety.ReducedProduct

set_option linter.style.haveILetI false

/-!
# Complete varieties

This module supplies a scheme-backed model of possibly non-affine varieties over an
algebraically closed field.  Objects are reduced separated finite-type `k`-schemes, morphisms are
scheme morphisms over `Spec k`, products are scheme fiber products, and closed subvarieties
are represented by closed immersions.  Presented affine varieties enter through the spectrum
of their reduced coordinate ring, with an explicit equivalence between scheme-valued points
and `Variety.Point`.  Rational points of a geometric product are explicitly identified with
pairs of rational points.

Completeness follows Borovoi, *Linear Algebraic Groups* (`Bor1`), Section 10.1 and its
reference AG.7.4: a variety is complete precisely when every projection after arbitrary base
change is a closed map.  Thus the definition is Mathlib's `UniversallyClosed` property of the
structure morphism.  We prove here that closed subvarieties stay complete and that a morphism
from a connected complete variety to a presented affine variety is constant.  The latter
uses the scheme-theoretic image: it is simultaneously affine, proper, and finite over the
base field, hence discrete; connectedness makes it a singleton.  Products remain in the
reduced carrier by the algebraically closed-field reduced-pullback theorem from AG.6.2.

The backward-completeness assertion in Bor1 10.1(4) is kept as an explicit source boundary
rather than stated for arbitrary carriers: the cited AG.18.3 proposition assumes that the
source is irreducible, while the present carrier permits disconnected schemes.  The exposed
`Geometric.IsIrreducible` predicate below records precisely that missing hypothesis.  The
transfer theorem therefore uses this hypothesis together with the stalkwise normality predicate
and the normalization/integral bridge; no disconnected extension is valid.  The repaired result
is implemented in `Theory.AlgebraicGroup.Variety.BijectiveNormalization`.
The module also exports the affine-local integrally-closed consequence of `Geometric.IsNormal`
and the universally-closed descent step used with the AG.18.3 normalization factorization.
The function-field/purely-inseparable argument itself lives in
`Theory.AlgebraicGroup.Variety.BijectiveNormalization`, keeping the carrier independent of that
higher normalization construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety

universe u

variable {k : Type u} [Field k]

/-- A possibly non-affine variety over `k`, represented as a reduced separated finite-type `k`-scheme. -/
structure Geometric (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The structure morphism to the base field. -/
  structureMap : toScheme ⟶ Spec (.of k)
  finiteType : LocallyOfFiniteType structureMap
  quasiCompact : QuasiCompact structureMap
  separated : IsSeparated structureMap
  reduced : IsReduced toScheme

namespace Geometric

instance (V : Geometric k) : LocallyOfFiniteType V.structureMap := V.finiteType
instance (V : Geometric k) : QuasiCompact V.structureMap := V.quasiCompact
instance (V : Geometric k) : IsSeparated V.structureMap := V.separated
instance (V : Geometric k) : IsReduced V.toScheme := V.reduced

/-- A rational point of a geometric variety is a section of its structure morphism. -/
def Point (V : Geometric k) :=
  {p : Spec (.of k) ⟶ V.toScheme // p ≫ V.structureMap = 𝟙 _}

/-- A genuine morphism of varieties: a scheme morphism commuting with structure maps. -/
structure Morphism (V W : Geometric k) where
  /-- The underlying scheme morphism. -/
  hom : V.toScheme ⟶ W.toScheme
  commutes : hom ≫ W.structureMap = V.structureMap

namespace Morphism

instance {V W : Geometric k} : CoeFun (Morphism V W) fun _ ↦ Point V → Point W where
  coe f x := ⟨x.1 ≫ f.hom, by rw [Category.assoc, f.commutes, x.2]⟩

@[simp] theorem coe_apply {V W : Geometric k} (f : Morphism V W) (x : Point V) :
    (f x).1 = x.1 ≫ f.hom := rfl

/-- The identity morphism. -/
@[simps] def id (V : Geometric k) : Morphism V V where
  hom := 𝟙 _
  commutes := Category.id_comp _

/-- Composition of geometric morphisms. -/
@[simps] def comp {U V W : Geometric k} (f : Morphism U V) (g : Morphism V W) :
    Morphism U W where
  hom := f.hom ≫ g.hom
  commutes := by rw [Category.assoc, g.commutes, f.commutes]

end Morphism

/-- The product of two varieties, formed as the scheme fiber product over `Spec k`. -/
def prod (V W : Geometric k) [IsAlgClosed k] : Geometric k where
  toScheme := pullback V.structureMap W.structureMap
  structureMap := pullback.fst V.structureMap W.structureMap ≫ V.structureMap
  finiteType := by infer_instance
  quasiCompact := by infer_instance
  separated := by infer_instance
  reduced := by
    exact isReduced_pullback_over_algClosed V.structureMap W.structureMap

/-- First projection from a product. -/
def fst (V W : Geometric k) [IsAlgClosed k] : Morphism (prod V W) V where
  hom := pullback.fst V.structureMap W.structureMap
  commutes := rfl

/-- Second projection from a product. -/
def snd (V W : Geometric k) [IsAlgClosed k] : Morphism (prod V W) W where
  hom := pullback.snd V.structureMap W.structureMap
  commutes := by
    change pullback.snd V.structureMap W.structureMap ≫ W.structureMap =
      pullback.fst V.structureMap W.structureMap ≫ V.structureMap
    exact pullback.condition.symm

/-- The rational point of a product induced by a pair of rational points. -/
noncomputable def prodPoint [IsAlgClosed k] {V W : Geometric k}
    (x : Point V) (y : Point W) : Point (prod V W) := by
  refine ⟨pullback.lift x.1 y.1 ?_, ?_⟩
  · rw [x.2, y.2]
  · change pullback.lift x.1 y.1 _ ≫
      pullback.fst V.structureMap W.structureMap ≫ V.structureMap = 𝟙 _
    rw [pullback.lift_fst_assoc, x.2]

@[simp] theorem fst_prodPoint [IsAlgClosed k] {V W : Geometric k}
    (x : Point V) (y : Point W) : fst V W (prodPoint x y) = x := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _

@[simp] theorem snd_prodPoint [IsAlgClosed k] {V W : Geometric k}
    (x : Point V) (y : Point W) : snd V W (prodPoint x y) = y := by
  apply Subtype.ext
  exact pullback.lift_snd _ _ _

/-- Rational points of a geometric product are pairs of rational points. -/
noncomputable def prodPointEquiv [IsAlgClosed k] (V W : Geometric k) :
    Point (prod V W) ≃ Point V × Point W where
  toFun z := (fst V W z, snd V W z)
  invFun z := prodPoint z.1 z.2
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv z := by simp

/-- A closed subvariety, represented by a closed immersion with its induced variety data. -/
structure ClosedSubvariety (V : Geometric k) where
  /-- The closed subvariety as a geometric variety. -/
  toGeometric : Geometric k
  /-- Its inclusion into the ambient variety. -/
  inclusion : Morphism toGeometric V
  isClosedImmersion : IsClosedImmersion inclusion.hom

instance {V : Geometric k} (Z : ClosedSubvariety V) :
    IsClosedImmersion Z.inclusion.hom := Z.isClosedImmersion

/-- Connectedness of the underlying Zariski space. -/
def IsConnected (V : Geometric k) : Prop := ConnectedSpace V.toScheme

/-- Irreducibility of the underlying Zariski space.

This is the source-faithful hypothesis required by AG.18.3 for the backward transfer of
completeness along a bijective morphism.  It is deliberately separate from `IsConnected`:
the carrier admits disconnected schemes, and the Bor1 10.1(4) formulation without this
hypothesis is false for such carriers.
-/
def IsIrreducible (V : Geometric k) : Prop := IrreducibleSpace V.toScheme

/-- Normality in the sense of AG.18.1: every local ring is an integrally closed domain. -/
def IsNormal (V : Geometric k) : Prop :=
  ∀ x : V.toScheme,
    IsDomain (V.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.toScheme.presheaf.stalk x)

/-!
The affine-local normality bridge is the scheme-theoretic form of the first step in Bor1 AG.18.3:
on an affine open `U`, every maximal localization of `Γ(U, 𝒪)` is the corresponding stalk.
`IsAffineOpen.isLocalization_stalk'` identifies that localization, and the local predicate in
`Geometric.IsNormal` supplies integral closedness.  Mathlib's maximal-localization criterion
then returns integral closedness of the affine section ring.  This is deliberately stated with
the domain instance explicit; the irreducible/reduced hypotheses needed to obtain that instance
belong to the caller's geometric argument.
-/
theorem affineSections_isIntegrallyClosed_of_isNormal
    {W : Geometric k} (hW : IsNormal W) {U : W.toScheme.Opens}
    (hU : IsAffineOpen U) [IsDomain Γ(W.toScheme, U)] :
    IsIntegrallyClosed Γ(W.toScheme, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P hP hPm
  letI := hPm
  letI : Algebra Γ(W.toScheme, U)
      (W.toScheme.presheaf.stalk
        (hU.fromSpec ⟨P, ‹P.IsMaximal›.isPrime⟩)).carrier :=
    W.toScheme.presheaf.algebra_section_stalk
      ⟨hU.fromSpec ⟨P, ‹P.IsMaximal›.isPrime⟩,
        (hU.isoSpec.inv ⟨P, ‹P.IsMaximal›.isPrime⟩).2⟩
  letI : IsLocalization.AtPrime
      (W.toScheme.presheaf.stalk
        (hU.fromSpec ⟨P, ‹P.IsMaximal›.isPrime⟩)).carrier P :=
    hU.isLocalization_stalk' ⟨P, ‹P.IsMaximal›.isPrime⟩
      (hU.isoSpec.inv ⟨P, ‹P.IsMaximal›.isPrime⟩).2
  exact (hW _).2.of_equiv
    (IsLocalization.algEquiv P.primeCompl
      (W.toScheme.presheaf.stalk
        (hU.fromSpec ⟨P, ‹P.IsMaximal›.isPrime⟩)).carrier
      (Localization.AtPrime P)).toRingEquiv

/-- Completeness in the sense of Bor1 10.1 / AG.7.4: the structure morphism is universally
closed, so every projection `V × X → X` is closed after arbitrary base change. -/
def IsComplete (V : Geometric k) : Prop := UniversallyClosed V.structureMap

/-!
This is the final universal-closedness transfer in Bor1 AG.18.3.  If an integral normalization
map `β : X ⟶ W` factors through `γ : X ⟶ V` and `γ` is surjective, then completeness of `W`
passes to `V`: integral morphisms are universally closed, composition with the complete
structure map is universally closed, and `UniversallyClosed.of_comp_surjective` descends that
property along the surjective factor.  The normalization factorization and its surjectivity are
intentionally hypotheses here; `exists_surjective_normalization_factorization_of_bijective` in
the higher `BijectiveNormalization` module constructs them from the AG.18.3 hypotheses.
-/
theorem isComplete_of_surjective_factorization_of_isIntegralHom
    {V W : Geometric k} (f : Morphism V W) (X : Scheme)
    (beta : X ⟶ W.toScheme) (gamma : X ⟶ V.toScheme)
    [IsIntegralHom beta] [Surjective gamma]
    (hfactor : beta = gamma ≫ f.hom) (hWcomplete : IsComplete W) :
    IsComplete V := by
  letI : UniversallyClosed W.structureMap := hWcomplete
  haveI : UniversallyClosed (beta ≫ W.structureMap) := by infer_instance
  have hcomp : gamma ≫ V.structureMap = beta ≫ W.structureMap := by
    rw [← f.commutes, ← Category.assoc, ← hfactor]
  haveI : UniversallyClosed (gamma ≫ V.structureMap) := hcomp ▸ inferInstance
  exact UniversallyClosed.of_comp_surjective gamma V.structureMap

/-- The projection-closedness formulation of completeness. -/
theorem isComplete_iff_projection_isClosedMap (V : Geometric k) :
    IsComplete V ↔
      ∀ (X : Scheme.{u}) (g : X ⟶ Spec (.of k)),
        IsClosedMap (pullback.fst g V.structureMap) := by
  rw [IsComplete, universallyClosed_iff]
  constructor
  · intro h X g
    exact h _ _ _ (IsPullback.of_hasPullback g V.structureMap)
  · intro h
    exact MorphismProperty.universally_mk' _ V.structureMap fun g ↦ h _ g

/-- A closed subvariety of a complete variety is complete. -/
theorem ClosedSubvariety.isComplete {V : Geometric k} (Z : ClosedSubvariety V)
    (hV : IsComplete V) : IsComplete Z.toGeometric := by
  let : UniversallyClosed V.structureMap := hV
  change UniversallyClosed Z.toGeometric.structureMap
  rw [← Z.inclusion.commutes]
  infer_instance

/-- Presented affine points, expressed as base-field-valued characters of the reduced
coordinate ring. -/
noncomputable def coordinateRingPointAlgHomEquiv [IsAlgClosed k]
    (V : Theory.AlgebraicGroup.Variety k) :
    V.Point ≃ (Theory.AlgebraicGroup.coordinateRing V →ₐ[k] k) :=
  (Theory.AlgebraicGroup.polynomialFunctionPointAlgHomEquiv V).trans
    ((Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).arrowCongr
      (AlgEquiv.refl : k ≃ₐ[k] k)).symm

/-- The scheme-backed geometric variety associated to a presented affine variety. -/
def ofAffine (V : Theory.AlgebraicGroup.Variety k) : Geometric k where
  toScheme := Spec (.of (Theory.AlgebraicGroup.coordinateRing V))
  structureMap := Spec.map (CommRingCat.ofHom
    (algebraMap k (Theory.AlgebraicGroup.coordinateRing V)))
  finiteType := by
    let : Algebra.FiniteType k (Theory.AlgebraicGroup.coordinateRing V) :=
      (Theory.AlgebraicGroup.polynomialFunction_finiteType V).equiv
        (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).symm
    exact AlgebraicGeometry.locallyOfFiniteType_specOverSpec
  quasiCompact := by infer_instance
  separated := by infer_instance
  reduced := by
    letI : IsReduced (Theory.AlgebraicGroup.coordinateRing V) :=
      isReduced_of_injective
        (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).toRingEquiv
        (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction V).injective
    infer_instance

/-- The rational point of the affine spectrum induced by a coordinate-ring character. -/
noncomputable def affinePointOfAlgHom [IsAlgClosed k]
    (V : Theory.AlgebraicGroup.Variety k)
    (φ : Theory.AlgebraicGroup.coordinateRing V →ₐ[k] k) : Point (ofAffine V) := by
  refine ⟨?_, ?_⟩
  · change Spec (.of k) ⟶ Spec (.of (Theory.AlgebraicGroup.coordinateRing V))
    exact Spec.map (CommRingCat.ofHom φ.toRingHom)
  · change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Theory.AlgebraicGroup.coordinateRing V))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of k) using 1
    rw [Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change φ (algebraMap k (Theory.AlgebraicGroup.coordinateRing V) r) = r
    exact φ.commutes r

/-- Rational points of an affine spectrum are coordinate-ring characters. -/
noncomputable def affinePointAlgHomEquiv [IsAlgClosed k]
    (V : Theory.AlgebraicGroup.Variety k) :
    Point (ofAffine V) ≃ (Theory.AlgebraicGroup.coordinateRing V →ₐ[k] k) where
  toFun p :=
    { toRingHom := (Spec.preimage p.1).hom
      commutes' := fun r ↦ by
        have h : CommRingCat.ofHom
              (algebraMap k (Theory.AlgebraicGroup.coordinateRing V)) ≫ Spec.preimage p.1 =
            𝟙 (CommRingCat.of k) := by
          apply Spec.map_injective
          simpa [ofAffine, Spec.map_comp] using p.2
        exact congr($h r) }
  invFun := affinePointOfAlgHom V
  left_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.preimage p.1) = p.1
    exact Spec.map_preimage p.1
  right_inv φ := by
    apply AlgHom.ext
    intro r
    change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom r = φ r
    simp

/-- The affine bridge on rational points.  This publicly identifies the rational-point type
of the scheme-backed object with the existing `Variety.Point` API. -/
def affinePointEquiv [IsAlgClosed k] (V : Theory.AlgebraicGroup.Variety k) :
    Point (ofAffine V) ≃ V.Point :=
  (affinePointAlgHomEquiv V).trans (coordinateRingPointAlgHomEquiv V).symm

/-- A morphism from a connected complete variety to a presented affine variety is constant
on rational points (Bor1 10.1(2)). -/
theorem morphism_to_affine_constant_of_isConnected_isComplete [IsAlgClosed k]
    {V : Geometric k} {A : Theory.AlgebraicGroup.Variety k}
    (f : Morphism V (ofAffine A)) (hVconnected : IsConnected V)
    (hVcomplete : IsComplete V) :
    ∀ x y : Point V, affinePointEquiv A (f x) = affinePointEquiv A (f y) := by
  letI : ConnectedSpace V.toScheme := hVconnected
  letI : UniversallyClosed V.structureMap := hVcomplete
  letI : UniversallyClosed (f.hom ≫ (ofAffine A).structureMap) := by
    rw [f.commutes]
    infer_instance
  letI : UniversallyClosed f.hom :=
    UniversallyClosed.of_comp_of_isSeparated f.hom (ofAffine A).structureMap
  letI : Surjective f.hom.toImage :=
    Surjective.of_universallyClosed_of_isDominant f.hom.toImage
  let q := f.hom.imageι ≫ (ofAffine A).structureMap
  letI : UniversallyClosed (f.hom.toImage ≫ q) := by
    dsimp only [q]
    rw [f.hom.toImage_imageι_assoc, f.commutes]
    infer_instance
  letI : UniversallyClosed q :=
    UniversallyClosed.of_comp_surjective f.hom.toImage q
  letI : IsProper q := IsProper.mk
  letI : IsAffine (ofAffine A).toScheme := by
    change IsAffine (Spec (.of (Theory.AlgebraicGroup.coordinateRing A)))
    infer_instance
  letI : IsAffine f.hom.image := isAffine_of_isAffineHom f.hom.imageι
  letI : IsAffineHom q := isAffineHom_of_isAffine q
  letI : IsFinite q :=
    (IsFinite.iff_isProper_and_isAffineHom (f := q)).mpr ⟨inferInstance, inferInstance⟩
  letI : ConnectedSpace f.hom.image :=
    f.hom.toImage.surjective.connectedSpace f.hom.toImage.continuous
  have hpreimage : q ⁻¹' {IsLocalRing.closedPoint k} =
      (Set.univ : Set f.hom.image) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hdiscrete : DiscreteTopology f.hom.image := by
    rw [← isDiscrete_univ_iff, ← hpreimage]
    exact q.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
  letI : DiscreteTopology f.hom.image := hdiscrete
  letI : Subsingleton f.hom.image :=
    subsingleton_of_preconnected_totallyDisconnected
  intro x y
  apply congrArg (affinePointEquiv A)
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq (ofAffine A).structureMap
      (f x).2 (f y).2
  change (x.1 ≫ f.hom) (IsLocalRing.closedPoint k) =
    (y.1 ≫ f.hom) (IsLocalRing.closedPoint k)
  rw [← f.hom.toImage_imageι]
  change f.hom.imageι (f.hom.toImage (x.1 (IsLocalRing.closedPoint k))) =
    f.hom.imageι (f.hom.toImage (y.1 (IsLocalRing.closedPoint k)))
  congr 1
  exact Subsingleton.elim _ _

end Geometric

end Theory.AlgebraicGroup.Variety
