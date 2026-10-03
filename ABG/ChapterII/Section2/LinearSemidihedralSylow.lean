module
public import Theory.SpecificGroups.GL2.QuadraticSemidihedralGenerators
public import GorensteinWalter.GL2DeterminantCard
public import ABG.ChapterII.Section1.SemidihedralGenerators

/-!
# The actual linear semidihedral Sylow subgroup

If the exact two-part of |F|+1 is 2^n with n≥2, the determinant-sign
subgroup of GL2(F) has a semidihedral Sylow two-subgroup of order 2^(n+2).
Its center maps into the actual scalar center of GL2(F). The assumptions
include F of order three; the rotation parameter n is not the source's
quasi-dihedral Sylow height.

The imported `finite_quadratic_semidihedral_generators` theorem supplies
the multiplication matrix of a quadratic-extension unit of order 2^(n+1)
and the Frobenius involution, with the exact semidihedral relation and
scalar half-power identity. The common generator theorem computes the
group and its center.
Every two-element has determinant of order at most two, since |F|−1 has
two-part two. The exact determinant-level cardinality then gives odd
index, proving Sylow maximality. The primitive unit's half-power is −1,
so the common center formula is the actual scalar involution.

This proves the linear semidihedral matrix model in
Alperin--Brauer--Gorenstein II.2 Lemma 1(i),(ii), article p17, used for the
model comparison in II.3 Proposition 3, article pp26–27. No abstract
matrix-group recognition or assumed Sylow shape enters the construction.
-/

namespace Matrix.GeneralLinearGroup

private theorem two_subgroup_le_sign_level
    (F : Type*) [Field F] [Finite F] (h4 : 4 ∣ Nat.card F + 1)
    (T : Subgroup (GL (Fin 2) F)) (hT : IsPGroup 2 T) :
    T ≤ determinantTwoPower F 1 := by
  intro a ha
  rw [mem_determinantTwoPower_iff_orderOf_dvd, pow_one]
  obtain ⟨k, hk⟩ := hT.exists_orderOf_dvd_pow (⟨a, ha⟩ : T)
  have hod : orderOf (det a) ∣ 2 ^ k := (orderOf_map_dvd det a).trans (by simpa using hk)
  obtain ⟨j, _hj, heq⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hod
  rw [heq]
  by_cases hj : j ≤ 1
  · simpa using Nat.pow_dvd_pow 2 hj
  · have hd4 : 4 ∣ Nat.card F - 1 := by
      have hd : 2 ^ j ∣ Nat.card F - 1 := by
        rw [← heq, ← Nat.card_units F]
        exact orderOf_dvd_natCard (det a)
      exact (show 4 ∣ 2 ^ j by simpa using Nat.pow_dvd_pow 2 (by omega : 2 ≤ j)).trans hd
    have hF : 1 < Nat.card F := Finite.one_lt_card
    omega

private theorem sign_level_card_two_part
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (hd : 2 ^ n ∣ Nat.card F + 1) (ho : Odd ((Nat.card F + 1) / 2 ^ n)) :
    ∃ r, Odd r ∧ Nat.card (determinantTwoPower F 1) = 2 ^ (n + 2) * r := by
  let q := Nat.card F
  obtain ⟨hqodd, _, _⟩ := quadratic_two_part_arithmetic q n hn hd ho
  have h4 : 4 ∣ q + 1 := (show 4 ∣ 2 ^ n by simpa using Nat.pow_dvd_pow 2 hn).trans hd
  obtain ⟨r, hr⟩ := hqodd
  have hro : Odd r := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    omega
  let k := (q + 1) / 2 ^ n
  have hk : q + 1 = 2 ^ n * k := (Nat.mul_div_cancel' hd).symm
  have hqo : Odd q := ⟨r, hr⟩
  refine ⟨q * r * k, (hqo.mul hro).mul ho, ?_⟩
  have hd1 : 2 ^ 1 ∣ Nat.card F - 1 := by change 2 ^ 1 ∣ q - 1; rw [hr]; simp
  rw [determinantTwoPower_card F 1 hd1]
  change 2 ^ 1 * q * (q ^ 2 - 1) = _
  have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hsq : q ^ 2 = (q - 1) * (q + 1) + 1 := by
      rw [hr]; simp only [Nat.add_sub_cancel]; ring
    omega
  rw [hs, show q - 1 = 2 * r by omega, hk, pow_add]
  ring

end Matrix.GeneralLinearGroup

namespace ABG
open Matrix.GeneralLinearGroup

public theorem determinantTwoPower_semidihedral_sylow
    (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (hn : 2 ≤ n) (hd : 2 ^ n ∣ Nat.card F + 1)
    (ho : Odd ((Nat.card F + 1) / 2 ^ n)) :
    ∃ S : Sylow 2 (determinantTwoPower F 1),
      Nat.card S = 2 ^ (n + 2) ∧ Stellmacher.IsSemidihedralGroup S ∧
      (Subgroup.center S).map ((determinantTwoPower F 1).subtype.comp (S : Subgroup _).subtype) ≤
        Subgroup.center (GL (Fin 2) F) := by
  let D := determinantTwoPower F 1
  obtain ⟨a, w, ha, hw, hout, hconj, hscalar⟩ :=
    finite_quadratic_semidihedral_generators F p n hn hd ho
  let T := Subgroup.zpowers a ⊔ Subgroup.zpowers w
  obtain ⟨hTcard, _, _⟩ := semidihedral_generated_subgroup_data hn a w ha hw hout hconj
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hTcard
  have h4 : 4 ∣ Nat.card F + 1 := (show 4 ∣ 2 ^ n by simpa using Nat.pow_dvd_pow 2 hn).trans hd
  have hTD : T ≤ D := two_subgroup_le_sign_level F h4 T hT2
  let aD : D := ⟨a, hTD ((show Subgroup.zpowers a ≤ T from le_sup_left) (Subgroup.mem_zpowers a))⟩
  let wD : D := ⟨w, hTD ((show Subgroup.zpowers w ≤ T from le_sup_right) (Subgroup.mem_zpowers w))⟩
  have haD : orderOf aD = 2 ^ (n + 1) := by
    rw [← orderOf_injective D.subtype D.subtype_injective]
    exact ha
  have hwD : wD ^ 2 = 1 := Subtype.ext hw
  have houtD : wD ∉ Subgroup.zpowers aD := by
    intro h
    apply hout
    have hm := Subgroup.mem_map_of_mem D.subtype h
    rwa [MonoidHom.map_zpowers] at hm
  have hconjD : wD * aD * wD⁻¹ = aD ^ (2 ^ n - 1) := Subtype.ext hconj
  let R := Subgroup.zpowers aD ⊔ Subgroup.zpowers wD
  obtain ⟨hRcard, hRshape, hRcenter⟩ := semidihedral_generated_subgroup_data hn aD wD haD hwD houtD hconjD
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hRcard
  obtain ⟨r, hr, hDcard⟩ := sign_level_card_two_part F n hn hd ho
  have hindex : R.index = r := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (n + 2))
    calc
      2 ^ (n + 2) * R.index = Nat.card R * R.index := by rw [hRcard]
      _ = Nat.card D := R.card_mul_index
      _ = 2 ^ (n + 2) * r := hDcard
  have hnot : ¬2 ∣ R.index := by rw [hindex]; exact Nat.not_even_iff_odd.mpr hr |>.comp (even_iff_two_dvd.mpr)
  let S := hR2.toSylow hnot
  refine ⟨S, hRcard, hRshape, ?_⟩
  change (Subgroup.center R).map (D.subtype.comp R.subtype) ≤ _
  rw [← Subgroup.map_map, hRcenter, MonoidHom.map_zpowers]
  change Subgroup.zpowers (a ^ (2 ^ n)) ≤ _
  rw [hscalar]
  apply Subgroup.zpowers_le.mpr
  apply Subgroup.mem_center_iff.mpr
  intro B
  exact (scalar_commute (-1 : Fˣ) B).symm

end ABG
