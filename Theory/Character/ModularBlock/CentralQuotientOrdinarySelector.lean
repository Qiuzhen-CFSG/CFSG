module

public import Theory.Character.ModularBlock.CentralQuotientSelector
public import Theory.Character.ModularBlock.BrauerConjugationTrace

/-!
# The ordinary principal selector under a central two-quotient

The proved residue-selector identity lifts to equality of the actual integral
selectors. Commuting idempotents with the same residue are equal: the standard
invertible idempotent intertwiner commutes with both. Coefficient extension
then identifies the quotient image of the ordinary complex selector.

All maps retain the prescribed cyclotomic root and contracted prime. This is
the ordinary-selector part of the central p-quotient argument in Feit,
*The Representation Theory of Finite Groups*, IV.4.12.
-/

public section
noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction BrauerBlockReduction CompatibleLocalBlock
  BlockOrthogonality BrauerConjugationTrace

private theorem commuting_idempotents_eq_of_map_eq {R k H : Type*} [CommRing R] [CommRing k] [Nontrivial k]
    [Group H] [Finite H]
    (f : R →+* k) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (a b : MonoidAlgebra R H) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hcomm : Commute a b)
    (hmap : MonoidAlgebra.mapRingHom H f a = MonoidAlgebra.mapRingHom H f b) : a = b := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let P := rightMatrix a
  let Q := rightMatrix b
  have hm : f.mapMatrix P = f.mapMatrix Q := by
    simpa only [P, Q, RingHom.mapMatrix_apply, ← rightMatrix_mapRingHom] using
      congrArg rightMatrix hmap
  have hc : Commute P Q := by
    have hc' : Commute (LinearMap.mulRight R a) (LinearMap.mulRight R b) := by
      change (LinearMap.mulRight R a).comp (LinearMap.mulRight R b) = _
      apply LinearMap.ext
      intro x
      change (x * b) * a = (x * a) * b
      rw [mul_assoc, mul_assoc, hcomm.eq]
    rw [show P = rightMatrix a from rfl, show Q = rightMatrix b from rfl,
      rightMatrix_eq_toMatrix, rightMatrix_eq_toMatrix]
    exact hc'.map (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis H R))
  obtain ⟨U, hU, hTU⟩ := Matrix.exists_unit_intertwiner_of_idempotent_map_eq
    f hf P Q (rightMatrix_isIdempotent a ha) (rightMatrix_isIdempotent b hb) hm
  have heq : P = Q := U.mul_right_inj.mp ((hTU P (Commute.refl P) hc).eq.symm.trans hU)
  ext x
  simpa [P, Q, rightMatrix] using congrArg (fun A : Matrix H H R => A x 1) heq

variable {G : Type*} [Group G] [Finite G]

/-- Reduction commutes with the actual quotient localization inclusion. -/
theorem compatibleQuotientLocalizationToResidue_commutes
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal] :
    (localizationToResidue d).comp (compatibleQuotientLocalizationInclusion d Z) =
      (compatibleQuotientResidueFieldInclusion d Z).comp
        (localizationToResidue (compatibleQuotientPrincipalCongruenceBlockData d Z)) := by
  apply IsLocalization.ringHom_ext
    (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [compatibleQuotientLocalizationInclusion_algebraMap,
    localizationToResidue_algebraMap, localizationToResidue_algebraMap]
  exact (compatibleQuotientResidueFieldInclusion_mk d Z a).symm

/-- The complex embedding commutes with the actual quotient localization inclusion. -/
theorem compatibleQuotientLocalizationToComplex_commutes
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal] :
    (IsotypicLattice.localizationToComplex d).comp
        (compatibleQuotientLocalizationInclusion d Z) =
      IsotypicLattice.localizationToComplex
        (compatibleQuotientPrincipalCongruenceBlockData d Z) := by
  apply IsLocalization.ringHom_ext
    (compatibleQuotientPrincipalCongruenceBlockData d Z).primeIdeal.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [compatibleQuotientLocalizationInclusion_algebraMap,
    IsotypicLattice.localizationToComplex_algebraMap,
    IsotypicLattice.localizationToComplex_algebraMap]
  exact Subring.coe_inclusion _ a

/-- The actual integral principal selector descends through a central two-quotient. -/
theorem mapDomain_localizedPrincipalBlockElement_eq_of_central_twoGroup
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) :
    MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
        (QuotientGroup.mk' Z) (localizedPrincipalBlockElement d) =
      MonoidAlgebra.mapRingHom (G ⧸ Z) (compatibleQuotientLocalizationInclusion d Z)
        (localizedPrincipalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d Z)) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d Z
  let a := MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
    (QuotientGroup.mk' Z) (localizedPrincipalBlockElement d)
  let b := MonoidAlgebra.mapRingHom (G ⧸ Z) (compatibleQuotientLocalizationInclusion d Z)
    (localizedPrincipalBlockElement q)
  apply commuting_idempotents_eq_of_map_eq (localizationToResidue d)
  · intro r hr
    exact not_not.mp fun hn => hr
      ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  · exact (localizedPrincipalBlockElement_isIdempotent d).map _
  · exact (localizedPrincipalBlockElement_isIdempotent q).map _
  · have hb : b ∈ Set.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) (G ⧸ Z)) :=
      mapRingHom_mem_center (compatibleQuotientLocalizationInclusion d Z) _
        (localizedPrincipalBlockElement_mem_center q)
    exact (Semigroup.mem_center_iff.mp hb a)
  · have hs := RingHom.congr_fun
      (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
        (localizationToResidue d) (QuotientGroup.mk' Z)) (localizedPrincipalBlockElement d)
    change MonoidAlgebra.mapRingHom (G ⧸ Z) (localizationToResidue d) a =
      MonoidAlgebra.mapDomainRingHom (principalResidueField d) (QuotientGroup.mk' Z)
        (reducedPrincipalBlockElement d) at hs
    rw [hs, mapDomain_reducedPrincipalBlockElement_eq_of_central_twoGroup d Z hcentral hZ]
    ext x
    simp only [reducedPrincipalBlockElement, reduceLocalizedGroupAlgebra,
      MonoidAlgebra.coeff_mapRingHom]
    exact (RingHom.congr_fun (compatibleQuotientLocalizationToResidue_commutes d Z)
      ((localizedPrincipalBlockElement q).coeff x)).symm

/-- The ordinary complex principal selector maps to the quotient's actual selector. -/
theorem mapDomain_principalBlockElement_eq_of_central_twoGroup
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) :
    MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z) (principalBlockElement d) =
      principalBlockElement (compatibleQuotientPrincipalCongruenceBlockData d Z) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d Z
  have hd := mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
    (IsotypicLattice.localizationToComplex d) (IsotypicLattice.localizationToComplex_algebraMap d)
  have hq := mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement q
    (IsotypicLattice.localizationToComplex q) (IsotypicLattice.localizationToComplex_algebraMap q)
  have hs := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (IsotypicLattice.localizationToComplex d) (QuotientGroup.mk' Z))
    (localizedPrincipalBlockElement d)
  change MonoidAlgebra.mapRingHom (G ⧸ Z) (IsotypicLattice.localizationToComplex d)
      (MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
        (QuotientGroup.mk' Z) (localizedPrincipalBlockElement d)) =
    MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z)
      (MonoidAlgebra.mapRingHom G (IsotypicLattice.localizationToComplex d)
        (localizedPrincipalBlockElement d)) at hs
  rw [hd, mapDomain_localizedPrincipalBlockElement_eq_of_central_twoGroup d Z hcentral hZ] at hs
  rw [← hs, ← hq]
  ext x
  simp only [MonoidAlgebra.coeff_mapRingHom]
  exact RingHom.congr_fun (compatibleQuotientLocalizationToComplex_commutes d Z)
    ((localizedPrincipalBlockElement q).coeff x)

end ModularBlock.Cartan
