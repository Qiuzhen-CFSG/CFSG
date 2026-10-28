module

public import Theory.Character.ModularBlock.PrimeOrthogonality
public import Theory.Character.ModularBlock.PrimeChange
public import Theory.Character.ModularBlock.PrimeIntersectionReduction

/-!
# Mixed-prime block intersection divisibility

If a finite group has no element of order `p * q` for distinct primes `p,q`,
the degree-weighted character sum over the intersection of any `p`-block and
any `q`-block, evaluated at a `p`-singular element, is divisible in the algebraic
integers by every power of `q` dividing the group order.

The same complete ordinary character family is retained by `atPrime`, so the
intersection is a literal intersection of finite row sets. Actual block column
orthogonality at both primes supplies the disjoint kernel supports in
`PrimeIntersectionReduction`. Averaging on a Sylow `q`-subgroup gives the
integral quotient by its order, and hence by the requested power of `q`.

Source: Brauer--Tuan, *On simple groups of finite order I* (1945), equation
(2.3) and Lemma 3, printed pp.764--765, equations (4.8)--(4.13).
-/

public section
noncomputable section
open scoped BigOperators
namespace BrauerTuan
open ModularBlock.PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Brauer--Tuan Lemma 3: the degree-weighted intersection sum of a `p`-block
and a `q`-block, at a `p`-singular element, is divisible in the algebraic integers
by every power of `q` dividing the group order, if no element has order `p * q`. -/
theorem isIntegral_block_intersection_sum_div_prime_pow
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (d : PrimeCongruenceBlockData p G) (i j : d.I)
    (hno : ∀ x : G, orderOf x ≠ p * q)
    (u : G) (hu : p ∣ orderOf u) (b : ℕ) (hb : q ^ b ∣ Nat.card G) :
    IsIntegral ℤ ((∑ k ∈ d.blockOf i ∩ (d.atPrime q).blockOf j,
      d.chi k (ConjClasses.mk 1) * d.chi k (ConjClasses.mk u)) / ((q ^ b : ℕ) : ℂ)) := by
  apply isIntegral_intersection_sum_div_prime_pow_of_orthogonality
    d.chi d.complete (d.blockOf i) ((d.atPrime q).blockOf j) hpq hno
    (fun a c ha hc =>
      ModularBlock.PrimeOrthogonality.block_column_eq_zero_of_singular_regular
        d i a c ha hc)
    (fun a c ha hc =>
      ModularBlock.PrimeOrthogonality.block_column_eq_zero_of_singular_regular
        (d.atPrime q) j a c ha hc) u hu b hb

end BrauerTuan
