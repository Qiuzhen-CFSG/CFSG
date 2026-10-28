module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Reduction

/-!
# The residue field of the specified congruence prime

The cyclotomic order is Dedekind and its nonzero prime has finite residue
field. Every homomorphism from its localization to a field of characteristic
`p` factors through this particular residue field: its kernel is a nonzero
prime of a DVR, hence the unique maximal ideal. Thus the arbitrary residue
map in `CompatibleRoots` uses the same congruences as the ordinary block.

Source: Feit, III.8--9, with the cyclotomic arithmetic of `CyclotomicDVR`.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.PrimeBlockConstruction
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

instance primeIdeal_isMaximal (d : PrimeCongruenceBlockData p G) :
    d.primeIdeal.IsMaximal := d.primeIdeal_maximal

abbrev residueField (d : PrimeCongruenceBlockData p G) :=
  cyclotomicOrder d.eta ⧸ d.primeIdeal

instance residueField_field (d : PrimeCongruenceBlockData p G) : Field (residueField d) :=
  Ideal.Quotient.field d.primeIdeal

@[expose] def toResidue (d : PrimeCongruenceBlockData p G) :
    Localization.AtPrime d.primeIdeal →+* residueField d :=
  IsLocalization.lift (M := d.primeIdeal.primeCompl)
    (S := Localization.AtPrime d.primeIdeal) (g := Ideal.Quotient.mk d.primeIdeal)
    (fun y => isUnit_iff_ne_zero.mpr (Ideal.Quotient.eq_zero_iff_mem.not.mpr y.2))

@[simp] theorem toResidue_algebraMap (d : PrimeCongruenceBlockData p G)
    (a : cyclotomicOrder d.eta) :
    toResidue d (algebraMap _ (Localization.AtPrime d.primeIdeal) a) =
      Ideal.Quotient.mk d.primeIdeal a := IsLocalization.lift_eq _ _

theorem toResidue_surjective (d : PrimeCongruenceBlockData p G) :
    Function.Surjective (toResidue d) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap _ _ a, toResidue_algebraMap d a⟩

theorem toResidue_eq_zero_iff (d : PrimeCongruenceBlockData p G)
    (a : Localization.AtPrime d.primeIdeal) :
    toResidue d a = 0 ↔ ¬ IsUnit a := by
  have hk := RingHom.ker_isMaximal_of_surjective (toResidue d) (toResidue_surjective d)
  rw [← RingHom.mem_ker, IsLocalRing.eq_maximalIdeal hk, IsLocalRing.mem_maximalIdeal]
  rfl

theorem primeIdeal_ne_bot (d : PrimeCongruenceBlockData p G) [Fact p.Prime] :
    d.primeIdeal ≠ ⊥ := by
  intro h
  have hp := PrimeSelector.prime_mem_primeIdeal d
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

instance localization_dvr (d : PrimeCongruenceBlockData p G) [Fact p.Prime] :
    IsDiscreteValuationRing (Localization.AtPrime d.primeIdeal) := by
  let : IsDedekindDomain (cyclotomicOrder d.eta) :=
    CyclotomicDVR.cyclotomicOrder_isDedekindDomain (Nat.card_pos (α := G)).ne' d.eta_spec
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (cyclotomicOrder d.eta) (primeIdeal_ne_bot d) (Localization.AtPrime d.primeIdeal)

instance residueField_finite (d : PrimeCongruenceBlockData p G) [Fact p.Prime] :
    Finite (residueField d) :=
  CyclotomicDVR.cyclotomicOrder_quotient_finite (Nat.card_pos (α := G)).ne'
    d.eta_spec d.primeIdeal (primeIdeal_ne_bot d)

instance residueField_charP (d : PrimeCongruenceBlockData p G) [Fact p.Prime] :
    CharP (residueField d) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    change Ideal.Quotient.mk d.primeIdeal (p : cyclotomicOrder d.eta) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (PrimeSelector.prime_mem_primeIdeal d))

/-- Any characteristic-p reduction has the canonical residue kernel. -/
theorem residue_ker (d : PrimeCongruenceBlockData p G) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p]
    (residue : Localization.AtPrime d.primeIdeal →+* K) :
    RingHom.ker residue = RingHom.ker (toResidue d) := by
  have hne : RingHom.ker residue ≠ ⊥ := by
    intro h
    have hp : (p : Localization.AtPrime d.primeIdeal) ∈ RingHom.ker residue := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  have hk : (RingHom.ker residue).IsMaximal :=
    (RingHom.ker_isPrime residue).isMaximal hne
  rw [IsLocalRing.eq_maximalIdeal hk,
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective (toResidue d) (toResidue_surjective d))]

/-- Factor the supplied map through the actual cyclotomic residue field. -/
theorem exists_residue_embedding (d : PrimeCongruenceBlockData p G) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p]
    (residue : Localization.AtPrime d.primeIdeal →+* K) :
    ∃ φ : residueField d →+* K, φ.comp (toResidue d) = residue := by
  let hker := le_of_eq (residue_ker d residue).symm
  exact ⟨(toResidue d).liftOfSurjective (toResidue_surjective d) ⟨residue, hker⟩,
    RingHom.liftOfSurjective_comp _ _ _⟩

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
