module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Theory.AlgebraicGroup.Bor1.ExactKernelClosedImageSeparableProjection
public import Theory.AlgebraicGroup.Bor1.FaithfullyFlatProjection
public import Theory.AlgebraicGroup.Bor1.InvariantPullbackSurjective
public import Theory.AlgebraicGroup.Bor1.QuotientUniversal
public import Theory.AlgebraicGroup.Variety.AffineDuality
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.Complete

/-!
# Geometric descent for Bor1 affine quotients

This module records the scheme-theoretic quotient data that is constructed in
the proof of `Theory.AlgebraicGroup.theorem_1_1_2_b`.  The companion
`Bor1.theorem_1_1_2_b_quotientData` keeps the quotient variety, its algebraic
group structure, the projection, point-surjectivity, exact point kernel, exact
identity-tangent kernel, identity-tangent surjectivity, the invariant-coordinate
pullback surjectivity, and the faithfully flat coordinate pullback.

The geometric descent theorem is the Bor1 quotient step needed by complete
orbit arguments.  A morphism from the affine geometric variety `ofAffine G` to
an arbitrary separated finite-type geometric target descends uniquely across
the quotient once its two pullbacks to the kernel pair of the quotient map
agree.  The proof converts the faithfully flat pullback on coordinate rings
into a flat surjective map of affine schemes and applies Mathlib's effective
epimorphism theorem for flat surjective affine morphisms.  The final clauses
identify the descended morphism on geometric rational points and, through the
canonical affine point equivalence, on the original presented `k`-points.
The comparison with `ofAffine_morphism` lets clients use the shared affine
morphism API without exposing this module's coordinate implementation.
-/

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Bor1

omit [IsAlgClosed k] in
private theorem geometricMorphism_ext {V W : Variety.Geometric k}
    (f g : Variety.Geometric.Morphism V W) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

omit [IsAlgClosed k] in
private noncomputable def affineGeometricMorphismAlgHom {V W : Variety k}
    (f : Variety.Morphism V W) :
    coordinateRing W →ₐ[k] coordinateRing V :=
  (coordinateRingAlgEquivPolynomialFunction V).symm.toAlgHom.comp
    (f.pullbackAlgHom.comp
      (coordinateRingAlgEquivPolynomialFunction W).toAlgHom)

/-- The scheme morphism between affine geometric varieties induced by a
presented affine-variety morphism. -/
public noncomputable def affineGeometricMorphism {V W : Variety k}
    (f : Variety.Morphism V W) :
    Variety.Geometric.Morphism
      (Variety.Geometric.ofAffine V) (Variety.Geometric.ofAffine W) where
  hom := Spec.map (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom)
  commutes := by
    change Spec.map (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing W))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing V)))
    rw [← Spec.map_comp]
    convert rfl using 1
    rw [Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change algebraMap k (coordinateRing V) r =
      affineGeometricMorphismAlgHom f (algebraMap k (coordinateRing W) r)
    exact ((affineGeometricMorphismAlgHom f).commutes r).symm

omit [IsAlgClosed k] in
/-- The descent construction agrees with the shared affine-to-scheme bridge. -/
public theorem affineGeometricMorphism_eq_ofAffine_morphism {V W : Variety k}
    (f : Variety.Morphism V W) :
    affineGeometricMorphism f = Variety.Geometric.ofAffine_morphism f := by
  rfl

private theorem affinePointAlgHomEquiv_affineGeometricMorphism
    {V W : Variety k} (f : Variety.Morphism V W)
    (x : Variety.Geometric.Point (Variety.Geometric.ofAffine V)) :
    Variety.Geometric.affinePointAlgHomEquiv W (affineGeometricMorphism f x) =
      (Variety.Geometric.affinePointAlgHomEquiv V x).comp
        (affineGeometricMorphismAlgHom f) := by
  apply AlgHom.ext
  intro a
  let xhom : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (coordinateRing V)) := x.1
  change
    (Spec.preimage
        (xhom ≫ Spec.map
          (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom))).hom a =
      (Spec.preimage xhom).hom ((affineGeometricMorphismAlgHom f) a)
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

private theorem affinePointEquiv_affineGeometricMorphism
    {V W : Variety k} (f : Variety.Morphism V W)
    (x : Variety.Geometric.Point (Variety.Geometric.ofAffine V)) :
    Variety.Geometric.affinePointEquiv W (affineGeometricMorphism f x) =
      f.toFun (Variety.Geometric.affinePointEquiv V x) := by
  apply (Variety.Geometric.coordinateRingPointAlgHomEquiv W).injective
  have hxcoord :
      Variety.Geometric.coordinateRingPointAlgHomEquiv V
          (Variety.Geometric.affinePointEquiv V x) =
        Variety.Geometric.affinePointAlgHomEquiv V x := by
    exact (Variety.Geometric.coordinateRingPointAlgHomEquiv V).apply_symm_apply
      (Variety.Geometric.affinePointAlgHomEquiv V x)
  apply AlgHom.ext
  intro a
  calc
    Variety.Geometric.coordinateRingPointAlgHomEquiv W
        (Variety.Geometric.affinePointEquiv W (affineGeometricMorphism f x)) a =
        Variety.Geometric.affinePointAlgHomEquiv W (affineGeometricMorphism f x) a := by
      exact congrArg (fun φ : coordinateRing W →ₐ[k] k => φ a)
        ((Variety.Geometric.coordinateRingPointAlgHomEquiv W).apply_symm_apply
          (Variety.Geometric.affinePointAlgHomEquiv W (affineGeometricMorphism f x)))
    _ = ((Variety.Geometric.affinePointAlgHomEquiv V x).comp
        (affineGeometricMorphismAlgHom f)) a := by
      exact congrArg (fun φ : coordinateRing W →ₐ[k] k => φ a)
        (affinePointAlgHomEquiv_affineGeometricMorphism f x)
    _ = Variety.Geometric.coordinateRingPointAlgHomEquiv W
        (f.toFun (Variety.Geometric.affinePointEquiv V x)) a := by
      have hxcoord_a := congrArg
        (fun φ : coordinateRing V →ₐ[k] k =>
          φ ((coordinateRingAlgEquivPolynomialFunction V).symm
            (f.pullbackAlgHom ((coordinateRingAlgEquivPolynomialFunction W) a))))
        hxcoord
      change ((Variety.Geometric.affinePointAlgHomEquiv V x)
          ((coordinateRingAlgEquivPolynomialFunction V).symm
            (f.pullbackAlgHom ((coordinateRingAlgEquivPolynomialFunction W) a)))) =
        polynomialFunctionPointAlgHom W (f.toFun (Variety.Geometric.affinePointEquiv V x))
          ((coordinateRingAlgEquivPolynomialFunction W) a)
      rw [← hxcoord_a]
      rw [show Variety.Geometric.coordinateRingPointAlgHomEquiv V
          (Variety.Geometric.affinePointEquiv V x) =
          coordinatePointAlgHom V (Variety.Geometric.affinePointEquiv V x) by rfl]
      simp [coordinatePointAlgHom]
      rfl

omit [IsAlgClosed k] in
private theorem affineGeometricMorphismAlgHom_faithfullyFlat
    {V W : Variety k} (f : Variety.Morphism V W)
    (hff : f.pullbackRingHom.FaithfullyFlat) :
    (affineGeometricMorphismAlgHom f).toRingHom.FaithfullyFlat := by
  dsimp [affineGeometricMorphismAlgHom]
  let eW := coordinateRingAlgEquivPolynomialFunction W
  let eV := coordinateRingAlgEquivPolynomialFunction V
  have hW : eW.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective eW.bijective
  have hf : f.pullbackAlgHom.toRingHom.FaithfullyFlat := by
    change f.pullbackRingHom.FaithfullyFlat
    exact hff
  have hcomp :
      (f.pullbackAlgHom.toRingHom.comp eW.toRingHom).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition
      eW.toRingHom f.pullbackAlgHom.toRingHom hW hf
  have hV : eV.symm.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective eV.symm.bijective
  exact RingHom.FaithfullyFlat.stableUnderComposition
    (f.pullbackAlgHom.toRingHom.comp eW.toRingHom)
    eV.symm.toRingHom hcomp hV

omit [IsAlgClosed k] in
private theorem affineGeometricMorphism_flat_and_surjective_of_faithfullyFlat
    {V W : Variety k} (f : Variety.Morphism V W)
    (hff : f.pullbackRingHom.FaithfullyFlat) :
    Flat (affineGeometricMorphism f).hom ∧
      Surjective (affineGeometricMorphism f).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom)) ∧
    Surjective (Spec.map (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom))
  exact (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (affineGeometricMorphismAlgHom f).toRingHom)).mpr
    (affineGeometricMorphismAlgHom_faithfullyFlat f hff)

/-- The quotient package constructed by the Bor1 proof of
`Theory.AlgebraicGroup.theorem_1_1_2_b`, retaining the geometric and coordinate
descent witnesses that the older theorem erases. -/
public structure Theorem112BQuotientData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) where
  quotient : Variety k
  quotientAlgebraicGroup : AlgebraicGroup quotient
  projection : @AlgebraicGroup.Morphism k _ G quotient inferInstance quotientAlgebraicGroup
  projectionToVariety : Variety.Morphism G quotient
  projection_toVariety : projection.toVariety = projectionToVariety
  pointSurjective : Function.Surjective projection.onPoints
  kernel_eq : projection.kernel = H.toSubgroup
  tangentKernel_eq :
    LinearMap.ker (identityTangentMorphismLinearMap projection) =
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion)
  tangentSurjective : Function.Surjective (identityTangentMorphismLinearMap projection)
  invariantPullbackSurjective :
    Function.Surjective
      (projection.pullbackToRightInvariantCoordinateRing H (by rw [kernel_eq]))
  coordinatePullbackFaithfullyFlat :
    projectionToVariety.pullbackRingHom.FaithfullyFlat
  algebraicUniversal :
    ∀ {I : Variety k} [hI : AlgebraicGroup I]
      (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∃! ψ : @AlgebraicGroup.Morphism k _ quotient I quotientAlgebraicGroup hI,
        ψ.comp projection = φ

/-- The Bor1 quotient construction with all descent witnesses retained. -/
public noncomputable def theorem_1_1_2_b_quotientData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : H.toSubgroup.Normal) :
    Theorem112BQuotientData H := by
  let P :=
    Classical.choice
      (Bor1.ClosedSubgroup.chevalleyWeightBlockExactDifferentialKernel_nonempty H hH)
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  let Q := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  let hπexists :=
    Bor1.ExactKernelDifferentialRationalRepresentation.closedImageProjection_exactTangentKernel_surjective_exists
      H P
  let π := Classical.choose hπexists
  have hπsurj : Function.Surjective π.onPoints :=
    (Classical.choose_spec hπexists).1
  have hπker : π.kernel = H.toSubgroup :=
    (Classical.choose_spec hπexists).2.1
  have hπtker :
      LinearMap.ker (identityTangentMorphismLinearMap π) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion) :=
    (Classical.choose_spec hπexists).2.2.1
  have hπdf : Function.Surjective (identityTangentMorphismLinearMap π) :=
    (Classical.choose_spec hπexists).2.2.2
  have hπpull : Function.Surjective
      (π.pullbackToRightInvariantCoordinateRing H (by rw [hπker])) :=
    Bor1.pullbackToRightInvariantCoordinateRing_surjective
      H π hπsurj hπker hπdf
  have hπff : π.toVariety.pullbackRingHom.FaithfullyFlat :=
    Bor1.pullbackRingHom_faithfullyFlat_of_surjective_of_tangent_surjective
      π hπsurj hπdf
  refine
    { quotient := Q.carrierVariety
      quotientAlgebraicGroup := inferInstance
      projection := π
      projectionToVariety := π.toVariety
      projection_toVariety := rfl
      pointSurjective := hπsurj
      kernel_eq := hπker
      tangentKernel_eq := hπtker
      tangentSurjective := hπdf
      invariantPullbackSurjective := hπpull
      coordinatePullbackFaithfullyFlat := hπff
      algebraicUniversal := ?_ }
  intro I hI φ hφ
  exact Bor1.quotient_universal_of_surjective_invariant_pullback
    H hH π hπsurj hπker hπpull hI φ hφ

/-- Effective descent of geometric morphisms across a faithfully flat affine
quotient map, with rational-point compatibility. -/
public theorem descend_geometric_morphism_of_kernel_pair_equal_of_faithfullyFlat
    {G Q : Variety k}
    (π : Variety.Morphism G Q)
    (hπff : π.pullbackRingHom.FaithfullyFlat)
    {X : Variety.Geometric k}
    (f : Variety.Geometric.Morphism (Variety.Geometric.ofAffine G) X)
    (hpair :
      pullback.fst (affineGeometricMorphism π).hom
          (affineGeometricMorphism π).hom ≫ f.hom =
        pullback.snd (affineGeometricMorphism π).hom
          (affineGeometricMorphism π).hom ≫ f.hom) :
    ∃! u : Variety.Geometric.Morphism (Variety.Geometric.ofAffine Q) X,
      (affineGeometricMorphism π).comp u = f ∧
        (∀ x : Variety.Geometric.Point (Variety.Geometric.ofAffine G),
          u ((affineGeometricMorphism π) x) = f x) ∧
        (∀ x : Variety.Point G,
          u ((Variety.Geometric.affinePointEquiv Q).symm (π.toFun x)) =
            f ((Variety.Geometric.affinePointEquiv G).symm x)) := by
  let πg := affineGeometricMorphism π
  have hflatSurj :
      Flat πg.hom ∧ Surjective πg.hom :=
    affineGeometricMorphism_flat_and_surjective_of_faithfullyFlat π hπff
  letI : Flat πg.hom := hflatSurj.1
  letI : Surjective πg.hom := hflatSurj.2
  haveI : IsAffine (Variety.Geometric.ofAffine G).toScheme := by
    change IsAffine (Spec (CommRingCat.of (coordinateRing G)))
    infer_instance
  haveI : IsAffine (Variety.Geometric.ofAffine Q).toScheme := by
    change IsAffine (Spec (CommRingCat.of (coordinateRing Q)))
    infer_instance
  haveI : IsRegularEpi πg.hom :=
    AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine πg.hom
  obtain ⟨uHom, huHom⟩ := IsRegularEpi.exists_of_isKernelPair
    πg.hom (IsPullback.of_hasPullback _ _) f.hom hpair
  have huComm : uHom ≫ X.structureMap = (Variety.Geometric.ofAffine Q).structureMap := by
    rw [← cancel_epi πg.hom]
    rw [← Category.assoc, huHom, f.commutes, πg.commutes]
  let u : Variety.Geometric.Morphism (Variety.Geometric.ofAffine Q) X :=
    { hom := uHom
      commutes := huComm }
  have hu : πg.comp u = f := by
    apply geometricMorphism_ext
    exact huHom
  have hcompat : ∀ x : Variety.Geometric.Point (Variety.Geometric.ofAffine G),
      u (πg x) = f x := by
    intro x
    apply Subtype.ext
    exact congrArg (fun m : Variety.Geometric.Morphism
        (Variety.Geometric.ofAffine G) X => (m x).1) hu
  have hcompatAffine : ∀ x : Variety.Point G,
      u ((Variety.Geometric.affinePointEquiv Q).symm (π.toFun x)) =
        f ((Variety.Geometric.affinePointEquiv G).symm x) := by
    intro x
    have hπpoint :
        πg ((Variety.Geometric.affinePointEquiv G).symm x) =
          (Variety.Geometric.affinePointEquiv Q).symm (π.toFun x) := by
      apply (Variety.Geometric.affinePointEquiv Q).injective
      rw [affinePointEquiv_affineGeometricMorphism]
      simp
    simpa [hπpoint.symm] using
      hcompat ((Variety.Geometric.affinePointEquiv G).symm x)
  refine ⟨u, ⟨hu, hcompat, hcompatAffine⟩, ?_⟩
  intro u' hu'
  apply geometricMorphism_ext
  have hleft := congrArg (fun m : Variety.Geometric.Morphism
      (Variety.Geometric.ofAffine G) X => m.hom) hu'.1
  have hright := congrArg (fun m : Variety.Geometric.Morphism
      (Variety.Geometric.ofAffine G) X => m.hom) hu
  change πg.hom ≫ u'.hom = f.hom at hleft
  change πg.hom ≫ u.hom = f.hom at hright
  rw [← cancel_epi πg.hom]
  exact hleft.trans hright.symm

/-- Descend a geometric morphism through the retained Bor1 quotient data when
the morphism agrees on the quotient kernel pair. -/
public theorem descend_geometric_morphism_of_kernel_pair_equal
    {G : Variety k} [AlgebraicGroup G] {H : ClosedSubgroup G}
    (D : Theorem112BQuotientData H)
    {X : Variety.Geometric k}
    (f : Variety.Geometric.Morphism (Variety.Geometric.ofAffine G) X)
    (hpair :
      pullback.fst (affineGeometricMorphism D.projectionToVariety).hom
          (affineGeometricMorphism D.projectionToVariety).hom ≫ f.hom =
        pullback.snd (affineGeometricMorphism D.projectionToVariety).hom
          (affineGeometricMorphism D.projectionToVariety).hom ≫ f.hom) :
    ∃! u : Variety.Geometric.Morphism (Variety.Geometric.ofAffine D.quotient) X,
      (affineGeometricMorphism D.projectionToVariety).comp u = f ∧
        (∀ x : Variety.Geometric.Point (Variety.Geometric.ofAffine G),
          u ((affineGeometricMorphism D.projectionToVariety) x) = f x) ∧
        (∀ x : Variety.Point G,
          u ((Variety.Geometric.affinePointEquiv D.quotient).symm
              (D.projectionToVariety.toFun x)) =
            f ((Variety.Geometric.affinePointEquiv G).symm x)) := by
  exact descend_geometric_morphism_of_kernel_pair_equal_of_faithfullyFlat
    D.projectionToVariety D.coordinatePullbackFaithfullyFlat f hpair

end Bor1

end Theory.AlgebraicGroup
