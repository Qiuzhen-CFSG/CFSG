module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.Scalars
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.Residue

/-!
# Nilpotence detected by ordinary central scalars

A uniform DVR exponent absorbs the group-order denominator in the character
coefficient formula. If all ordinary central scalars are nonunits, a positive
power of the central element reduces to zero. This works at every prime.

Adapted from `ModularBlock/ScalarReconstruction.lean` and
`ScalarNilpotence.lean`, ported from `public/lean-eval/glauberman_zStar`
at c3503435. Source: Feit III.8--9.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators
variable {p : ℕ}

private def characterValueInCyclotomicOrder
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G) (i : d.I) (g : G) :
    cyclotomicOrder d.eta := by
  refine ⟨d.chi i (ConjClasses.mk g), ?_⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact representation_character_mem_cyclotomicOrder d.eta_spec rho g

@[simp] private theorem coe_characterValueInCyclotomicOrder
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G) (i : d.I) (g : G) :
    ((characterValueInCyclotomicOrder d i g : cyclotomicOrder d.eta) : ℂ) =
      d.chi i (ConjClasses.mk g) := rfl

@[simp] private theorem localizationToComplex_characterValue
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I) (g : G) :
    localizationToComplex d.primeIdeal
        (algebraMap (cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (characterValueInCyclotomicOrder d i g)) =
      d.chi i (ConjClasses.mk g) := by
  rw [localizationToComplex_algebraMap, coe_characterValueInCyclotomicOrder]


private theorem card_mul_coeff_eq_sum_localizedCentralScalar
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (g : G) :
    (Nat.card G : Localization.AtPrime d.primeIdeal) * z.1.coeff g =
      ∑ i : d.I,
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z *
          algebraMap (cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i 1) *
          algebraMap (cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i g⁻¹) := by
  classical
  apply PrimeIntegralModels.localizationToComplex_injective d.primeIdeal
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



variable [Fact p.Prime]

/-- If every ordinary scalar of a central localized element is a nonunit,
then one positive power of that element vanishes after reduction.  The
uniform DVR exponent absorbs the single denominator `|G|` in the central
coefficient formula. -/

theorem exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hscalar : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z)) :
    ∃ N : ℕ, 0 < N ∧
      MonoidAlgebra.mapRingHom G
          (toResidue d)
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : IsDiscreteValuationRing R :=
    localization_dvr d
  have hcard : (Nat.card G : R) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  obtain ⟨N, hN, huniform⟩ :=
    ModularBlock.BlockPrimitivity.exists_uniform_pow_eq_mul_nonunit (R := R)
      (Nat.card G : R) hcard
  have hquot : ∀ i : d.I, ∃ q : R,
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N =
          (Nat.card G : R) * q ∧
        ¬ IsUnit q := by
    intro i
    exact huniform _ (hscalar i)
  choose q hq hq_nonunit using hquot
  refine ⟨N, hN, ?_⟩
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom]
  apply (toResidue_eq_zero_iff d _).2
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  have hreconstruct :=
    card_mul_coeff_eq_sum_localizedCentralScalar d (z ^ N) g
  simp_rw [localizedCentralScalar_pow_of_pos d _ z N hN] at hreconstruct
  have hcoeff :
      ((z ^ N : Subring.center
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1.coeff g) =
        ∑ i : d.I,
          q i *
            algebraMap (cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) := by
    apply mul_left_cancel₀ hcard
    calc
      (Nat.card G : R) *
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1.coeff g) =
        ∑ i : d.I,
          CentralScalarCongruence.localizedCentralScalar d.eta_spec
                d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N *
              algebraMap (cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) :=
        hreconstruct
      _ = ∑ i : d.I,
          ((Nat.card G : R) * q i) *
              algebraMap (cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hq i]
      _ = (Nat.card G : R) *
          ∑ i : d.I,
            q i *
                algebraMap (cyclotomicOrder d.eta) R
                  (characterValueInCyclotomicOrder d i 1) *
              algebraMap (cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i g⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hcoeff]
  apply Ideal.sum_mem
  intro i _hi
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  rw [IsLocalRing.mem_maximalIdeal]
  exact hq_nonunit i


end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
