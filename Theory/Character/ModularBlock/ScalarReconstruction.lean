module

public import Theory.Character.ModularBlock.ScalarAlgebra
public import Theory.Character.ModularBlock.CharacterProjectorDefs

/-!
# Recovering central coefficients from localized character scalars

The complex central coefficient formula expresses the group order times a
coefficient as a sum of irreducible scalar values, degrees, and inverse
character values. Each character value lies in the cyclotomic order.
Injectivity of the canonical embedding of its localization into the complex
numbers transfers the formula to the integral localization itself.

Ported from the coefficient reconstruction step of
`c3503435:glauberman_zStar/Submission/ZStar/BlockPrimitivity.lean`.
This denominator-cleared formula lets the DVR argument prove that a power
of a central element has all coefficients in the maximal ideal.
-/

public section
noncomputable section
namespace ModularBlock.BlockPrimitivity
open BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

@[simp] private theorem localizationToComplex_characterValue
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) (g : G) :
    localizationToComplex d.primeIdeal
        (algebraMap (cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (IsotypicLattice.characterValueInCyclotomicOrder d i g)) =
      d.chi i (ConjClasses.mk g) := by
  rw [localizationToComplex_algebraMap, IsotypicLattice.coe_characterValueInCyclotomicOrder]


theorem card_mul_coeff_eq_sum_localizedCentralScalar
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (g : G) :
    (Nat.card G : Localization.AtPrime d.primeIdeal) * z.1.coeff g =
      ∑ i : d.I,
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z *
          algebraMap (cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (IsotypicLattice.characterValueInCyclotomicOrder d i 1) *
          algebraMap (cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (IsotypicLattice.characterValueInCyclotomicOrder d i g⁻¹) := by
  classical
  apply localizationToComplex_injective d
  simp only [map_mul, map_sum, map_natCast,
    localizationToComplex_characterValue]
  change (Nat.card G : ℂ) *
      (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) z.1).coeff g =
    ∑ i : d.I,
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) *
        d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹)
  let zC := MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) z.1
  have hzC : zC ∈ Set.center (MonoidAlgebra ℂ G) :=
    groupAlgebra_mapRingHom_mem_center (localizationToComplex d.primeIdeal) z.1 z.property
  have hcoeff :=
    BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
      d.chi d.complete zC (Semigroup.mem_center_iff.mp hzC)
      (fun i => localizationToComplex d.primeIdeal
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z))
      (by
        intro i n rho hrho
        exact localizedCentralScalar_action d i rho hrho z) g
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  change zC.coeff g = _ at hcoeff
  change (Nat.card G : ℂ) * zC.coeff g = _
  rw [hcoeff]
  field_simp [hcard]


end ModularBlock.BlockPrimitivity

