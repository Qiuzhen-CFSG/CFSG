module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# The cubic residual of a group with symmetric-three core quotient

If A/O₂(A) is S₃, its order is six times a power of two. Hence A is a
{2,3}-group and O²(A)=O^{3′}(A). This identifies the literal residuals
used in the fixed-line comparison of Aschbacher–Smith 13.4.7, printed
pp.899–900; it does not identify either residual with the two-core.
-/

public section
open Subgroup Theory.GroupTheory
namespace SymmetricThreeTwoCore
variable {A : Type*} [Group A] [Finite A]

theorem twoThree_of_quotient (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hcard : Nat.card A = 6 * 2 ^ n := by rw [card_eq e,hn]
  rw [IsPiGroup_iff]
  intro p hp
  rw [hcard] at hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hp with hs | ht
  · rcases p.property.dvd_mul.mp (show p.val ∣ 2 * 3 from hs) with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow ht) |>.resolve_left p.property.ne_one)

theorem twoResidual_eq_primeToThree (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    pResidual 2 A = primeToResidual 3 A :=
  twoResidual_eq_primeToResidual_three (twoThree_of_quotient e)

end SymmetricThreeTwoCore
