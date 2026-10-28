module
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSubgroups
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Field parity from a solvable symplectic Sylow overgroup

A solvable subgroup of Sp4(2^n), n > 1, containing a Sylow two-subgroup
normalizes that Sylow subgroup. Its cubic subgroups therefore embed in the
split torus, whose order divides (2^n - 1)^2. A cubic element forces n even.

This is the intrinsic field restriction used for the remaining symplectic
row in Aschbacher--Smith, original 15.2.23, printed p.1116, together with
the solvable Sylow-overgroup argument of Proposition 1.3.4, p.511.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A cubic in a solvable Sylow overgroup forces an even defining degree. -/
theorem solvable_sylow_overgroup_degree_even {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 (Sp F)) (A : Subgroup (Sp F))
    (hs : Group.IsSolvable A) (hPA : (P : Subgroup (Sp F)) ≤ A)
    (hthree : 3 ∣ Nat.card A) : Even n := by
  have hlarge : 2 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  have hnorm := solvable_sylow_overgroup_normalizes hlarge P A hs hPA
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 hthree
  let B := (zpowers a).map A.subtype
  have hb : Nat.card B = 3 := by
    rw [card_map_of_injective A.subtype_injective,Nat.card_zpowers,ha]
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hb)
  have hd := (odd_sylow_normalizer_abelian_card hF (by omega) P
    ((map_subtype_le _).trans hnorm) (by decide : Odd 3) hp).2
  rw [hb] at hd
  have ht : 3 ∣ 2 ^ n - 1 := Nat.prime_three.dvd_of_dvd_pow hd
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp ht
end Theory.SpecificGroups.SymplecticFour
