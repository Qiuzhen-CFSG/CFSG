module

public import Theory.AlgebraicGroup.Bor1.MorphicActionClosedOrbit
public import Theory.AlgebraicGroup.Variety.GeometricPointBijectivity

/-!
# The affine quotient and a complete closed orbit

For an action of an affine algebraic group, a closed orbit has its actual
reduced orbit carrier as a closed subvariety, and hence inherits completeness.
The orbit is irreducible when the acting group is connected.

When the point stabilizer is normal in the acting group, the genuine descended
orbit morphism factors regularly through this closed immersion. Faithful flatness
of the quotient projection proves scheme-point surjectivity of that projection
and transfers irreducibility. Its exact point kernel proves injectivity of the
descended orbit map; the closed-point orbit description proves surjectivity.
The rational-point bijectivity theorem then gives bijectivity on scheme points.
No separability or scheme isomorphism is inferred from this bijection.

Source: Borel, *Linear Algebraic Groups*, §10.4, the quotient-to-closed-orbit
step (refs/KGroup/Bor1/Chapter3.tex, lines 851–859).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k]

private theorem affineMorphism_surjective_of_faithfullyFlat
    {V W : Theory.AlgebraicGroup.Variety k} (f : Variety.Morphism V W)
    (hff : f.pullbackRingHom.FaithfullyFlat) :
    Surjective (Bor1.affineGeometricMorphism f).hom := by
  rw [Bor1.affineGeometricMorphism_eq_ofAffine_morphism]
  have hW : (coordinateRingAlgEquivPolynomialFunction W).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
    (coordinateRingAlgEquivPolynomialFunction W).bijective
  have hV : (coordinateRingAlgEquivPolynomialFunction V).symm.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
    (coordinateRingAlgEquivPolynomialFunction V).symm.bijective
  have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
    (coordinateRingAlgEquivPolynomialFunction W).toRingHom
    f.pullbackRingHom hW hff
  have h := RingHom.FaithfullyFlat.stableUnderComposition
    (f.pullbackRingHom.comp (coordinateRingAlgEquivPolynomialFunction W).toRingHom)
    (coordinateRingAlgEquivPolynomialFunction V).symm.toRingHom hcomp hV
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (ofAffinePullback f).toRingHom)).mpr h).2

private noncomputable def liftToClosedImmersion
    {V W Z : Geometric k} (i : Morphism Z V) [IsClosedImmersion i.hom]
    (f : Morphism W V) (hf : Set.range f.hom ⊆ Set.range i.hom) : Morphism W Z := by
  let S : Closeds V.toScheme := ⟨Set.range i.hom, i.hom.isClosedEmbedding.isClosed_range⟩
  have hi : i.hom.ker ≤ Scheme.IdealSheafData.vanishingIdeal S :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp i.hom.range_subset_ker_support
  have hker : i.hom.ker ≤ f.hom.ker :=
    hi.trans (vanishingIdeal_le_ker_of_isReduced S f.hom hf)
  exact { hom := IsClosedImmersion.lift i.hom f.hom hker
          commutes := by
            rw [← i.commutes, ← Category.assoc, IsClosedImmersion.lift_fac, f.commutes] }

private theorem liftToClosedImmersion_fac
    {V W Z : Geometric k} (i : Morphism Z V) [IsClosedImmersion i.hom]
    (f : Morphism W V) (hf : Set.range f.hom ⊆ Set.range i.hom) :
    (liftToClosedImmersion i f hf).comp i = f := by
  apply Morphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

private theorem injective_points_of_mono
    {V W : Geometric k} (i : Morphism V W) [Mono i.hom] :
    Function.Injective (fun x : Point V => i x) := by
  intro x y h
  apply Subtype.ext
  apply (cancel_mono i.hom).mp
  exact congrArg Subtype.val h

namespace MorphicAction
variable [IsAlgClosed k]
variable {H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup H]
variable {X : Geometric k} (A : MorphicAction H X)

/-- A closed orbit has a closed immersion as its actual orbit inclusion. -/
public theorem orbitSubvariety_isClosedImmersion (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom)) :
    IsClosedImmersion (A.orbitSubvariety x).inclusion.hom := by
  apply IsClosedImmersion.of_isPreimmersion
  rwa [A.orbitSubvariety_range x]

/-- A closed orbit in a complete variety is complete. -/
public theorem orbitSubvariety_isComplete (hX : IsComplete X) (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom)) :
    IsComplete (A.orbitSubvariety x).toGeometric := by
  letI := A.orbitSubvariety_isClosedImmersion x hclosed
  letI : UniversallyClosed X.structureMap := hX
  rw [IsComplete, ← (A.orbitSubvariety x).inclusion.commutes]
  infer_instance

/-- A closed orbit of a connected affine algebraic group is irreducible. -/
public theorem orbitSubvariety_isIrreducible_of_isClosed
    (hH : Variety.IsConnected H) (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom)) :
    IsIrreducible (A.orbitSubvariety x).toGeometric := by
  letI := A.orbitSubvariety_isClosedImmersion x hclosed
  let i := (A.orbitSubvariety x).inclusion
  have hrange : Set.range (A.orbitMorphismAt x).hom ⊆ Set.range i.hom := by
    rw [A.orbitSubvariety_range x]
  let f := liftToClosedImmersion i (A.orbitMorphismAt x) hrange
  have hfac : f.comp i = A.orbitMorphismAt x := liftToClosedImmersion_fac _ _ _
  have hsurj : Function.Surjective f.hom := by
    intro z
    have hz : i.hom z ∈ Set.range (A.orbitMorphismAt x).hom := by
      rw [← A.orbitSubvariety_range x]
      exact ⟨z, rfl⟩
    obtain ⟨g, hg⟩ := hz
    refine ⟨g, i.hom.isEmbedding.injective ?_⟩
    exact (congrArg (fun t : Morphism (ofAffine H) X => t.hom g) hfac).trans hg
  letI : IrreducibleSpace (ofAffine H).toScheme := ofAffine_isIrreducible_of_isConnected H hH
  exact hsurj.irreducibleSpace f.hom.continuous

private theorem projectionToVariety_surjective (x : Point X)
    (D : Bor1.Theorem112BQuotientData (A.pointStabilizer x)) :
    Function.Surjective D.projectionToVariety.toFun := by
  rw [← D.projection_toVariety]
  exact D.pointSurjective

private theorem quotient_orbit_injective_points (x : Point X)
    (D : Bor1.Theorem112BQuotientData (A.pointStabilizer x))
    (f : Morphism (ofAffine D.quotient) X)
    (hf : ∀ g : Theory.AlgebraicGroup.Variety.Point H,
      f ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g)) =
        A.toMulAction.smul g x) :
    Function.Injective (fun q : Point (ofAffine D.quotient) => f q) := by
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point H) (Point X) := A.toMulAction
  intro q r hqr
  obtain ⟨g, hg⟩ := A.projectionToVariety_surjective x D (affinePointEquiv D.quotient q)
  obtain ⟨h, hh⟩ := A.projectionToVariety_surjective x D (affinePointEquiv D.quotient r)
  have hq : (affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g) = q := by
    rw [hg, Equiv.symm_apply_apply]
  have hr : (affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun h) = r := by
    rw [hh, Equiv.symm_apply_apply]
  have ha : g • x = h • x := by
    change A.toMulAction.smul g x = A.toMulAction.smul h x
    rw [← hf g, ← hf h, hq, hr]
    exact hqr
  have hstab : g⁻¹ * h ∈ (A.pointStabilizer x).toSubgroup := by
    apply (A.mem_pointStabilizer x _).mpr
    change (g⁻¹ * h) • x = x
    rw [mul_smul, ← ha, inv_smul_smul]
  rw [← D.kernel_eq] at hstab
  change D.projection.onPoints (g⁻¹ * h) = 1 at hstab
  rw [map_mul, map_inv, inv_mul_eq_one] at hstab
  apply (affinePointEquiv D.quotient).injective
  rw [← hg, ← hh, ← D.projection_toVariety]
  exact hstab

private theorem orbitSubvariety_point_in_orbit (x : Point X)
    (y : Point (A.orbitSubvariety x).toGeometric) :
    ∃ g : Theory.AlgebraicGroup.Variety.Point H,
      A.toMulAction.smul g x = (A.orbitSubvariety x).inclusion y := by
  let z := (A.orbitSubvariety x).inclusion y
  have hz : z.1 (IsLocalRing.closedPoint k) ∈ A.orbitSupport x := by
    rw [A.orbitSupport_eq_range_inter_closedPoints x]
    refine ⟨?_, (pointEquivClosedPoint X.structureMap z).2⟩
    rw [← A.orbitSubvariety_range x]
    exact ⟨y.1 (IsLocalRing.closedPoint k), rfl⟩
  rw [A.orbitSupport_eq_rationalPointSupport_range x,
    rationalPointSupport_eq_closedPoint_image] at hz
  obtain ⟨w, ⟨g, rfl⟩, hw⟩ := hz
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact ext_of_apply_closedPoint_eq X.structureMap (A.toMulAction.smul g x).2 z.2 hw

/-- The actual stabilizer quotient maps bijectively onto the actual closed orbit;
its source is irreducible if the acting group is connected. -/
public theorem exists_bijective_quotient_to_closed_orbit
    (hH : Variety.IsConnected H) (x : Point X)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (hN : (A.pointStabilizer x).toSubgroup.Normal) :
    ∃ D : Bor1.Theorem112BQuotientData (A.pointStabilizer x),
      ∃ v : Morphism (ofAffine D.quotient) (A.orbitSubvariety x).toGeometric,
        IsIrreducible (ofAffine D.quotient) ∧ Function.Bijective v.hom ∧
        ∀ g : Theory.AlgebraicGroup.Variety.Point H,
          (A.orbitSubvariety x).inclusion
            (v ((affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g))) =
              A.toMulAction.smul g x := by
  obtain ⟨D, f, hfac, hf⟩ := A.exists_quotient_orbit_morphism x hN
  let π := Bor1.affineGeometricMorphism D.projectionToVariety
  have hπ : Surjective π.hom :=
    affineMorphism_surjective_of_faithfullyFlat _ D.coordinatePullbackFaithfullyFlat
  have hirr : IsIrreducible (ofAffine D.quotient) := by
    letI : IrreducibleSpace (ofAffine H).toScheme := ofAffine_isIrreducible_of_isConnected H hH
    exact hπ.surj.irreducibleSpace π.hom.continuous
  have hrange : Set.range f.hom ⊆ Set.range (A.orbitSubvariety x).inclusion.hom := by
    rw [A.orbitSubvariety_range x]
    rintro _ ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := hπ.surj q
    refine ⟨g, ?_⟩
    exact (congrArg (fun t : Morphism (ofAffine H) X => t.hom g) hfac).symm
  letI := A.orbitSubvariety_isClosedImmersion x hclosed
  let v := liftToClosedImmersion (A.orbitSubvariety x).inclusion f hrange
  have hvfac : v.comp (A.orbitSubvariety x).inclusion = f :=
    liftToClosedImmersion_fac _ _ _
  have hvpoint (q : Point (ofAffine D.quotient)) :
      (A.orbitSubvariety x).inclusion (v q) = f q :=
    congrArg (fun t : Morphism (ofAffine D.quotient) X => t q) hvfac
  have hvbij : Function.Bijective (fun q : Point (ofAffine D.quotient) => v q) := by
    constructor
    · intro q r hqr
      apply A.quotient_orbit_injective_points x D f hf
      rw [← hvpoint q, ← hvpoint r, hqr]
    · intro y
      obtain ⟨g, hg⟩ := A.orbitSubvariety_point_in_orbit x y
      refine ⟨(affinePointEquiv D.quotient).symm (D.projectionToVariety.toFun g), ?_⟩
      apply injective_points_of_mono (A.orbitSubvariety x).inclusion
      rw [hvpoint, hf, hg]
  refine ⟨D, v, hirr, v.bijective_hom_of_bijective_points hvbij, ?_⟩
  intro g
  rw [hvpoint, hf]

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric
