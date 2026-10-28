module

public import Theory.Character.ModularBlock.PrimeCongruence

/-!
# Changing the prime of a congruence character family

Choose a prime above `q` while retaining the given complete ordinary character
family and its cyclotomic order. In particular, blocks at two different primes
are finite sets in the same index type, so their intersection is literal.
Existence follows from lying over for the integral cyclotomic order.

Source: Brauer--Tuan, *On simple groups of finite order I* (1945), §2 and
Lemma 3, where the same ordinary characters are partitioned at two primes.
-/

public section
noncomputable section
namespace ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- Retain the ordinary rows and choose a maximal ideal above the new prime. -/
@[expose] def atPrime (d : PrimeCongruenceBlockData p G) (q : ℕ) [Fact q.Prime] :
    PrimeCongruenceBlockData q G where
  I := d.I
  fintypeI := d.fintypeI
  decidableEqI := d.decidableEqI
  chi := d.chi
  complete := d.complete
  eta := d.eta
  eta_spec := d.eta_spec
  primeIdeal := (exists_maximalIdeal_above_prime d.eta_spec q).choose
  primeIdeal_maximal := (exists_maximalIdeal_above_prime d.eta_spec q).choose_spec.1
  primeIdeal_liesOver := (exists_maximalIdeal_above_prime d.eta_spec q).choose_spec.2
  principal := d.principal
  principal_eq := d.principal_eq

@[simp] theorem atPrime_chi (d : PrimeCongruenceBlockData p G)
    (q : ℕ) [Fact q.Prime] : (d.atPrime q).chi = d.chi := rfl

@[simp] theorem atPrime_principal (d : PrimeCongruenceBlockData p G)
    (q : ℕ) [Fact q.Prime] : (d.atPrime q).principal = d.principal := rfl

end ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData
