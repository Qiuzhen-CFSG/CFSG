module

public import Theory.Character.ModularBlock.BlockBimoduleTrace
public import Theory.Character.ModularBlock.CentralQuotientBimoduleTrace
public import Theory.Character.ModularBlock.CentralQuotientOrdinarySelector

/-!
# Reduction of the central two-quotient ordinary kernel comparison

The ordinary principal-block kernel is the trace of left/right multiplication
on its block algebra. The actual integral selector maps to the compatible
quotient selector. Consequently, integral trace scaling gives the exact
ordinary character-kernel comparison, with no conjugation of either value.

This module supplies that reduction. The remaining input is trace scaling
for an integral central idempotent under a central two-subgroup quotient; it
must hold before reduction, so that the integer multiplicity `|Z|` is retained.
No Cartan or decomposition-matrix identity is assumed.

Source: Feit, *The Representation Theory of Finite Groups*, IV.4.12.
-/

public section
noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction BlockOrthogonality CompatibleLocalBlock BlockBimoduleTrace

variable {G : Type*} [Group G] [Finite G]

/-- The ordinary kernel comparison is precisely the projected trace comparison
for the ordinary selector and its quotient image. -/
theorem ordinaryKernel_centralTwo_iff_trace_scaling
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) (g h : G) :
    (∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
      (Nat.card Z : ℂ) *
        ∑ i ∈ (compatibleQuotientPrincipalCongruenceBlockData d Z).block,
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z g)) *
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z h))) ↔
    (LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedBimultiplication (principalBlockElement d) g h) =
      (Nat.card Z : ℂ) * LinearMap.trace ℂ (MonoidAlgebra ℂ (G ⧸ Z))
        (projectedBimultiplication
          (MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z) (principalBlockElement d))
          (QuotientGroup.mk' Z g) (QuotientGroup.mk' Z h))) := by
  rw [mapDomain_principalBlockElement_eq_of_central_twoGroup d Z hcentral hZ,
    principalBlock_bimultiplication_trace, principalBlock_bimultiplication_trace]

/-- Exact integral trace scaling suffices for the ordinary kernel comparison.
The trace hypothesis is over the localization, not its characteristic-two residue. -/
theorem ordinaryKernel_eq_of_centralTwo_integralTrace
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) (g h : G)
    (htrace :
      LinearMap.trace (Localization.AtPrime d.primeIdeal)
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
          (projectedBimultiplication (localizedPrincipalBlockElement d) g h) =
        (Nat.card Z : Localization.AtPrime d.primeIdeal) *
          LinearMap.trace (Localization.AtPrime d.primeIdeal)
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) (G ⧸ Z))
            (projectedBimultiplication
              (MonoidAlgebra.mapDomainRingHom (Localization.AtPrime d.primeIdeal)
                (QuotientGroup.mk' Z) (localizedPrincipalBlockElement d))
              (QuotientGroup.mk' Z g) (QuotientGroup.mk' Z h))) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
      (Nat.card Z : ℂ) *
        ∑ i ∈ (compatibleQuotientPrincipalCongruenceBlockData d Z).block,
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z g)) *
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z h)) := by
  apply (ordinaryKernel_centralTwo_iff_trace_scaling d Z hcentral hZ g h).mpr
  have h := congrArg (IsotypicLattice.localizationToComplex d) htrace
  rw [map_mul, map_natCast, map_trace_projectedBimultiplication,
    map_trace_projectedBimultiplication] at h
  have hd := mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
    (IsotypicLattice.localizationToComplex d) (IsotypicLattice.localizationToComplex_algebraMap d)
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
  rwa [hs, hd] at h

/-- The ordinary principal-block kernel comparison for odd-order elements. -/
theorem ordinaryKernel_centralTwo
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z) (g h : G)
    (hg : Odd (orderOf g)) (hh : Odd (orderOf h)) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
      (Nat.card Z : ℂ) *
        ∑ i ∈ (compatibleQuotientPrincipalCongruenceBlockData d Z).block,
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z g)) *
          (compatibleQuotientPrincipalCongruenceBlockData d Z).chi i
            (ConjClasses.mk (QuotientGroup.mk' Z h)) := by
  apply ordinaryKernel_eq_of_centralTwo_integralTrace d Z hcentral hZ g h
  exact integralTrace_centralTwo_quotient d Z hcentral hZ
    (localizedPrincipalBlockElement d)
    (localizedPrincipalBlockElement_isIdempotent d)
    (localizedPrincipalBlockElement_mem_center d) g h hg hh

end ModularBlock.Cartan
