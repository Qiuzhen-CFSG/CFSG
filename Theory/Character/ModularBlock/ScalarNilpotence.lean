module

public import Theory.Character.ModularBlock.ScalarReconstruction
public import Theory.Character.ModularBlock.ResidueKernel
public import Theory.Character.ModularBlock.DVRDenominators
public import Theory.Character.ModularBlock.CyclotomicDVR

/-!
# Nilpotence after reduction from nonunit character scalars

If every localized ordinary central scalar of a central element is a nonunit,
one positive power reduces to zero. A uniform DVR exponent makes each scalar
power divisible by the group order with a nonunit quotient. The coefficient
reconstruction formula then cancels the group-order denominator and writes
each coefficient as a sum in the maximal ideal. The localization residue map
kills precisely that ideal, equivalently precisely the nonunits.

Ported from lines 824-945 of
`c3503435:glauberman_zStar/Submission/ZStar/BlockPrimitivity.lean`.
This is the nilpotence input that forces a nonzero reduced idempotent to have
a nonzero ordinary scalar, the key step in principal-block primitivity.
-/

public section
noncomputable section
namespace ModularBlock.BlockPrimitivity
open BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

/-- If every ordinary scalar of a central localized element is a nonunit,
then one positive power of that element vanishes after reduction.  The
uniform DVR exponent absorbs the single denominator `|G|` in the central
coefficient formula. -/

theorem exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hscalar : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z)) :
    ∃ N : ℕ, 0 < N ∧
      MonoidAlgebra.mapRingHom G
          (BrauerBlockReduction.localizationToResidue d)
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  have hcard : (Nat.card G : R) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  obtain ⟨N, hN, huniform⟩ :=
    exists_uniform_pow_eq_mul_nonunit (R := R)
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
  apply (localizationToResidue_eq_zero_iff_not_isUnit d _).2
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
              (IsotypicLattice.characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (IsotypicLattice.characterValueInCyclotomicOrder d i g⁻¹) := by
    apply mul_left_cancel₀ hcard
    calc
      (Nat.card G : R) *
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1.coeff g) =
        ∑ i : d.I,
          CentralScalarCongruence.localizedCentralScalar d.eta_spec
                d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N *
              algebraMap (cyclotomicOrder d.eta) R
                (IsotypicLattice.characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (IsotypicLattice.characterValueInCyclotomicOrder d i g⁻¹) :=
        hreconstruct
      _ = ∑ i : d.I,
          ((Nat.card G : R) * q i) *
              algebraMap (cyclotomicOrder d.eta) R
                (IsotypicLattice.characterValueInCyclotomicOrder d i 1) *
            algebraMap (cyclotomicOrder d.eta) R
              (IsotypicLattice.characterValueInCyclotomicOrder d i g⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hq i]
      _ = (Nat.card G : R) *
          ∑ i : d.I,
            q i *
                algebraMap (cyclotomicOrder d.eta) R
                  (IsotypicLattice.characterValueInCyclotomicOrder d i 1) *
              algebraMap (cyclotomicOrder d.eta) R
                (IsotypicLattice.characterValueInCyclotomicOrder d i g⁻¹) := by
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

end ModularBlock.BlockPrimitivity

