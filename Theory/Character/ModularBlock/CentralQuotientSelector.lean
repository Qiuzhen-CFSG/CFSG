module

public import Theory.Character.ModularBlock.PrincipalPrimitivity
public import Theory.Character.ModularBlock.QuotientRepresentation
public import Theory.Character.ModularBlock.CentralPQuotientPrimitivity

/-!
# Principal selectors and compatible quotient coefficients

The quotient's principal selector, extended to the ambient finite residue
field, is a primitive central idempotent of augmentation one. For a central
two-subgroup quotient, the image of the ambient reduced selector is also
primitive, so the two selectors coincide. The commutative square for the
prescribed splitting-field equivalence then gives the exact selector identity
over the splitting field.

This isolates the coefficient and uniqueness steps in the central two-subgroup
quotient argument (Feit, *The Representation Theory of Finite Groups*, IV.4.12).
All coefficient maps use the actual contracted prime. Quotient primitivity
follows from the centrally generated nilpotent kernel; no block correspondence
is assumed.
-/

public section
noncomputable section

namespace ModularBlock.Cartan

open PrincipalBlockConstruction BrauerBlockReduction BrauerCoefficientExtension
  CompatibleLocalBlock

universe u
variable {G : Type u} [Group G] [Finite G]

private theorem augmentation_mapDomain
    {R M N : Type*} [CommSemiring R] [Monoid M] [Monoid N]
    (f : M →* N) (a : MonoidAlgebra R M) :
    groupAlgebraAugmentation R N (MonoidAlgebra.mapDomainRingHom R f a) =
      groupAlgebraAugmentation R M a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single g r => simp

/-- The quotient's reduced principal selector stays primitive in the
ambient residue field at the prescribed prime. -/
theorem quotientPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal] :
    IsCentrallyPrimitive
      (MonoidAlgebra.mapRingHom (G ⧸ N)
        (compatibleQuotientResidueFieldInclusion d N)
        (reducedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d N))) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let k := principalResidueField q
  let K := principalResidueField d
  let φ := compatibleQuotientResidueFieldInclusion d N
  let : Field k := Ideal.Quotient.field q.primeIdeal
  let : Field K := Ideal.Quotient.field d.primeIdeal
  let : Finite K := FiniteFieldPrimitivity.principalResidueField_finite d
  let : Algebra k K := φ.toAlgebra
  exact FiniteFieldPrimitivity.map_isCentrallyPrimitive_of_augmentation_eq_one
    k K (G ⧸ N) (reducedPrincipalBlockElement q)
    (BlockPrimitivity.reducedPrincipalBlockElement_isCentrallyPrimitive q)
    (reducedPrincipalBlockElement_augmentation_eq_one q)

/-- Primitivity of the quotient image identifies the two actual residue-field
selectors: their intersection has augmentation one and hence is nonzero. -/
theorem mapDomain_reducedPrincipalBlockElement_eq_of_isCentrallyPrimitive
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hprimitive : IsCentrallyPrimitive
      (MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d))) :
    MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (compatibleQuotientResidueFieldInclusion d N)
        (reducedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  apply CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
    hprimitive (quotientPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive d N)
  intro hzero
  have haug := congrArg (groupAlgebraAugmentation (principalResidueField d) (G ⧸ N)) hzero
  rw [map_mul, augmentation_mapDomain, reducedPrincipalBlockElement_augmentation_eq_one,
    groupAlgebraAugmentation_mapRingHom,
    reducedPrincipalBlockElement_augmentation_eq_one, map_one, one_mul, map_zero] at haug
  exact one_ne_zero haug

/-- The compatible residue-selector identity transports to the exact
splitting-field identity consumed by principal-block inflation. -/
theorem mapDomain_splittingSelector_eq_of_reduced_image_isCentrallyPrimitive
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hprimitive : IsCentrallyPrimitive
      (MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d))) :
    MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' N)
        (splittingSelector d) =
      MonoidAlgebra.mapRingHom (G ⧸ N) (quotientSplittingFieldEquiv d N : _ →+* _)
        (splittingSelector (compatibleQuotientPrincipalCongruenceBlockData d N)) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have hsquare : (residueInclusion d).comp (compatibleQuotientResidueFieldInclusion d N) =
      (quotientSplittingFieldEquiv d N : _ →+* _).comp (residueInclusion q) := by
    ext x
    exact (quotientSplittingFieldEquiv_residueInclusion d N x).symm
  have hcomm := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (residueInclusion d) (QuotientGroup.mk' N)) (reducedPrincipalBlockElement d)
  change MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion d)
      (MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' N)
        (reducedPrincipalBlockElement d)) =
    MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' N)
      (splittingSelector d) at hcomm
  rw [← hcomm, mapDomain_reducedPrincipalBlockElement_eq_of_isCentrallyPrimitive d N hprimitive]
  change (MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion d)).comp
      (MonoidAlgebra.mapRingHom (G ⧸ N) (compatibleQuotientResidueFieldInclusion d N))
      (reducedPrincipalBlockElement q) =
    (MonoidAlgebra.mapRingHom (G ⧸ N) (quotientSplittingFieldEquiv d N : _ →+* _)).comp
      (MonoidAlgebra.mapRingHom (G ⧸ N) (residueInclusion q))
      (reducedPrincipalBlockElement q)
  rw [← MonoidAlgebra.mapRingHom_comp, ← MonoidAlgebra.mapRingHom_comp, hsquare]

/-- Quotienting by a central two-subgroup identifies the actual principal
selectors over the ambient residue field at the contracted prime. -/
theorem mapDomain_reducedPrincipalBlockElement_eq_of_central_twoGroup
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) :
    MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' Z)
        (reducedPrincipalBlockElement d) =
      MonoidAlgebra.mapRingHom (G ⧸ Z) (compatibleQuotientResidueFieldInclusion d Z)
        (reducedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d Z)) := by
  let : Finite (principalResidueField d) :=
    FiniteFieldPrimitivity.principalResidueField_finite d
  apply mapDomain_reducedPrincipalBlockElement_eq_of_isCentrallyPrimitive
  exact mapDomain_isCentrallyPrimitive_of_central_twoGroup Z hcentral hZ
    (reducedPrincipalBlockElement d)
    (BlockPrimitivity.reducedPrincipalBlockElement_isCentrallyPrimitive d)

/-- The principal selector descends through a central two-subgroup quotient
under the prescribed splitting-field equivalence. -/
theorem mapDomain_splittingSelector_eq_of_central_twoGroup
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) :
    MonoidAlgebra.mapDomainRingHom (splittingField d) (QuotientGroup.mk' Z)
        (splittingSelector d) =
      MonoidAlgebra.mapRingHom (G ⧸ Z) (quotientSplittingFieldEquiv d Z : _ →+* _)
        (splittingSelector (compatibleQuotientPrincipalCongruenceBlockData d Z)) := by
  apply mapDomain_splittingSelector_eq_of_reduced_image_isCentrallyPrimitive
  rw [mapDomain_reducedPrincipalBlockElement_eq_of_central_twoGroup d Z hcentral hZ]
  exact quotientPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive d Z

end ModularBlock.Cartan
