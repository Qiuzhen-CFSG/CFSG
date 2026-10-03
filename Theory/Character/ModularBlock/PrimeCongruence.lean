module

public import Theory.Character.ModularBlock.Congruence

/-!
# Ordinary congruence blocks at an arbitrary prime

A maximal ideal above a prime in the cyclotomic integer ring partitions the
actual irreducible characters by equality of reduced central characters.
This extends the prime-two construction without changing its interface.
Lying over constructs the data, and every block retains its congruence
criterion. These definitions support cyclic odd-prime blocks and comparisons
of blocks at different primes.

Source: Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51
(1945), pp.756--757, equation (2.2).
-/

public section
noncomputable section
namespace ModularBlock
namespace PrimeBlockConstruction
open BlockPreliminaries PrincipalBlockConstruction

/-- A maximal ideal above any prime in the cyclotomic integer ring. -/
theorem exists_maximalIdeal_above_prime
    {G : Type*} [Group G] [Finite G] {η : ℂ}
    (hη : IsPrimitiveRoot η (Nat.card G)) (p : ℕ) [Fact p.Prime] :
    ∃ P : Ideal (cyclotomicOrder η),
      P.IsMaximal ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  let : Algebra.IsIntegral ℤ (cyclotomicOrder η) :=
    Algebra.isIntegral_def.mpr fun z =>
      (isIntegral_algebraMap_iff
        (show Function.Injective (algebraMap (cyclotomicOrder η) ℂ) from
          Subtype.val_injective)).mp
        (isIntegral_cyclotomicOrder_element_of_isIntegral_generator
          (hη.isIntegral (Nat.card_pos (α := G))) z)
  let : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.span ({(p : ℤ)} : Set ℤ))

/-- A complete family of actual characters with a chosen prime above `p`.
All blocks, not only the principal block, use this same family. -/
structure PrimeCongruenceBlockData (p : ℕ)
    (G : Type*) [Group G] [Finite G] where
  I : Type
  fintypeI : Fintype I
  decidableEqI : DecidableEq I
  chi : I → ConjClassFunction G
  complete : IsCompleteIrreducibleCharacterFamily chi
  eta : ℂ
  eta_spec : IsPrimitiveRoot eta (Nat.card G)
  primeIdeal : Ideal (cyclotomicOrder eta)
  primeIdeal_maximal : primeIdeal.IsMaximal
  primeIdeal_liesOver : primeIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
  principal : I
  principal_eq : chi principal = ordinaryPrincipalCharacter G

namespace PrimeCongruenceBlockData
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

instance (d : PrimeCongruenceBlockData p G) : Fintype d.I := d.fintypeI
instance (d : PrimeCongruenceBlockData p G) : DecidableEq d.I := d.decidableEqI

/-- Equality of central-character reductions defines the block relation. -/
@[expose] def SameBlock (d : PrimeCongruenceBlockData p G) (i j : d.I) : Prop :=
  reducedCentralCharacter d.eta_spec d.primeIdeal (d.chi i) (d.complete.1 i) =
    reducedCentralCharacter d.eta_spec d.primeIdeal (d.chi j) (d.complete.1 j)

/-- The ordinary block containing an arbitrary row. -/
@[expose] def blockOf (d : PrimeCongruenceBlockData p G) (j : d.I) : Finset d.I := by
  classical
  exact Finset.univ.filter fun i => d.SameBlock i j

/-- The principal ordinary block at `p`. -/
@[expose] def block (d : PrimeCongruenceBlockData p G) : Finset d.I :=
  d.blockOf d.principal

@[simp] theorem mem_blockOf_iff (d : PrimeCongruenceBlockData p G) (i j : d.I) :
    i ∈ d.blockOf j ↔ d.SameBlock i j := by
  classical
  simp [blockOf]

@[simp] theorem self_mem_blockOf (d : PrimeCongruenceBlockData p G) (i : d.I) :
    i ∈ d.blockOf i := by
  rw [mem_blockOf_iff]
  rfl

@[simp] theorem principal_mem (d : PrimeCongruenceBlockData p G) :
    d.principal ∈ d.block := d.self_mem_blockOf _

/-- Membership is exactly congruence of every integral central-character value. -/
theorem mem_blockOf_iff_centralCharacter (d : PrimeCongruenceBlockData p G)
    (i j : d.I) :
    i ∈ d.blockOf j ↔ ∀ C : ConjClasses G,
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i) C -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j) (d.complete.1 j) C ∈
          d.primeIdeal := by
  rw [mem_blockOf_iff]
  exact sameTwoBlock_iff _ _ _ _ _ _

end PrimeCongruenceBlockData

/-- Congruence-block data exist at every prime, without block-theoretic assumptions. -/
theorem exists_primeCongruenceBlockData (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] : Nonempty (PrimeCongruenceBlockData p G) := by
  classical
  obtain ⟨d⟩ := exists_principalCongruenceBlockData G
  obtain ⟨P, hPmax, hPover⟩ := exists_maximalIdeal_above_prime d.eta_spec p
  exact ⟨{
    I := d.I
    fintypeI := d.fintypeI
    decidableEqI := d.decidableEqI
    chi := d.chi
    complete := d.complete
    eta := d.eta
    eta_spec := d.eta_spec
    primeIdeal := P
    primeIdeal_maximal := hPmax
    primeIdeal_liesOver := hPover
    principal := d.principal
    principal_eq := d.principal_eq }⟩

end PrimeBlockConstruction
end ModularBlock
