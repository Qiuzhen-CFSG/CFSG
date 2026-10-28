module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.NormalClosure
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Orders and Sylow transitivity in prime binary degree

For an action with semilinear zero stabilizer KΓ, field order 2ⁿ, and
|Γ| = n odd, every Sylow two-subgroup has order 2ⁿ and is transitive.
The stabilizer has odd order, so evaluation at zero is injective on a Sylow
subgroup; equal cardinalities make this evaluation surjective.

For prime n, Fermat's theorem gives coprimality of n and 2ⁿ−1. The standard
Mersenne gcd identity shows that a divisor 2ʳ−1 of the group order, with
1 < r < n, must equal n. These are the order calculations in GLS, Volume 4,
Chapter 1, Lemma 3.9 and the final argument of Theorem 3.2
(`refs/KGroup/GLS4/Chapter1.tex`, lines 438–468).
-/

public section

namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

/-- A positive binary Mersenne number is odd. -/
lemma mersenne_coprime_two {k : ℕ} (hk : 0 < k) : Nat.Coprime (2 ^ k - 1) 2 := by
  apply Nat.coprime_two_right.mpr
  have hpow : Even (2 ^ k) := even_two.pow_of_ne_zero (by omega)
  exact (Nat.odd_sub (Nat.one_le_pow k 2 (by decide))).mpr (by simpa using hpow)

/-- The prime degree does not divide the scalar subgroup order. -/
lemma prime_coprime_mersenne {n : ℕ} (hn : n.Prime) :
    Nat.Coprime n (2 ^ n - 1) := by
  let : Fact n.Prime := ⟨hn⟩
  apply hn.coprime_iff_not_dvd.mpr
  intro hd
  have hz : ((2 ^ n - 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hp : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  rw [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, ZMod.pow_card] at hz
  have he : (1 : ZMod n) = 0 := by linear_combination hz
  exact one_ne_zero he

/-- A smaller nontrivial center divisor can only be the prime degree. -/
lemma small_mersenne_eq_prime {n r : ℕ} (hn : n.Prime) (hr : 1 < r) (hrn : r < n)
    (hd : 2 ^ r - 1 ∣ 2 ^ n * (2 ^ n - 1) * n) : 2 ^ r - 1 = n := by
  have hcop : Nat.Coprime (2 ^ r - 1) (2 ^ n - 1) := by
    change Nat.gcd _ _ = 1
    rw [Nat.pow_sub_one_gcd_pow_sub_one]
    have hg : Nat.gcd r n = 1 :=
      (hn.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrn)).symm
    simp [hg]
  have hdn : 2 ^ r - 1 ∣ n :=
    (((mersenne_coprime_two (by omega : 0 < r)).pow_right n).mul_right hcop).dvd_of_dvd_mul_left hd
  rcases (Nat.dvd_prime hn).mp hdn with h | h
  · have hh : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
    norm_num at hh
    omega
  · exact h

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
  [MulAction X F] [FaithfulSMul X F]

omit [Finite X] [Finite F] in
/-- The literal scalar subgroup has the order of the field unit group. -/
lemma scalar_card (c : Coordinates X F) :
    Nat.card c.scalarSubgroup = Nat.card F - 1 := by
  rw [← Nat.card_units]
  exact Nat.card_congr (MonoidHom.ofInjective c.scalar_injective).symm.toEquiv

/-- The full binary part of the ambient order is the field cardinality. -/
lemma sylow_card (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hn : Odd n) (hnpos : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n) (S : Sylow 2 X) :
    Nat.card S = 2 ^ n := by
  have hX : Nat.card X = 2 ^ n * ((2 ^ n - 1) * n) := by
    rw [c.card_group, hF, hΓ, mul_assoc]
  have hodd : Nat.Coprime 2 ((2 ^ n - 1) * n) :=
    (mersenne_coprime_two hnpos).symm.mul_right (Nat.coprime_two_left.mpr hn)
  apply Nat.dvd_antisymm
  · obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hd := S.card_subgroup_dvd_card
    rw [hk, hX] at hd
    rw [hk]
    exact (hodd.pow_left k).dvd_of_dvd_mul_right hd
  · apply S.pow_dvd_card_of_pow_dvd_card
    rw [hX]
    exact dvd_mul_right _ _

/-- Odd point stabilizers make the Sylow two-subgroup regular, hence transitive. -/
lemma sylow_transitive (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hn : Odd n) (hnpos : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n) (S : Sylow 2 X) :
    IsPretransitive S F := by
  have hS := sylow_card c hn hnpos hF hΓ S
  have hd : Disjoint (S : Subgroup X) (stabilizer X (0 : F)) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hS, c.card_stabilizer, hF, hΓ]
    exact ((mersenne_coprime_two hnpos).symm.mul_right
      (Nat.coprime_two_left.mpr hn)).pow_left n
  have hinj : Function.Injective (fun s : S => (s : X) • (0 : F)) := by
    intro s t hst
    change (s : X) • (0 : F) = (t : X) • (0 : F) at hst
    apply Subtype.ext
    apply inv_mul_eq_one.mp
    apply (Subgroup.disjoint_def.mp hd) ((S : Subgroup X).mul_mem
      ((S : Subgroup X).inv_mem s.property) t.property)
    change ((s : X)⁻¹ * t) • (0 : F) = 0
    rw [mul_smul, ← hst, inv_smul_smul]
  have hsurj : Function.Surjective (fun s : S => (s : X) • (0 : F)) :=
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hS.trans hF.symm⟩).2
  apply (isPretransitive_iff_orbit_eq_univ (0 : F)).mpr
  apply Set.eq_univ_of_forall
  intro x
  exact mem_orbit_iff.mpr (hsurj x)

end MulAction.SemilinearPointStabilizer.PrimeExclusion
