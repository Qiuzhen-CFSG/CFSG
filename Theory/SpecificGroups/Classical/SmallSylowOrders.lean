module

public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.GroupTheory.SmallSylowObstructions

/-!
# Small Sylow tests for odd classical groups

Sixteen divides the orders of odd-field PSL₃ and PSU₃: the adjacent-square
factor supplies eight and the odd-degree factor supplies two; the scalar
quotient has odd order. An elementary Sylow of odd-field PSL₂ is the
four-group, since its actual dihedral rotation has order at most two.
The order formula then forces the field order to be 3 or 5 modulo eight.

Source: Huppert II.6.14, II.8.3–4, II.10.12; Aschbacher–Smith F.6.17–18,
printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.ClassicalSmallSylow
private theorem psl3_card_gcd {F : Type*} [Field F] [Finite F] :
    Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [Fin.prod_univ_succ] at h
  have h₁ : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  have h₂ : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  calc
    _ = (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := h
    _ = _ := by rw [h₁, h₂]; ring

theorem sixteen_dvd_psl3_odd {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) : 16 ∣ Nat.card PSL(3,F) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have hc : 1 ≤ q ^ 3 := by nlinarith
  have h8 : 8 ∣ q ^ 2 - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hm : q % 8 < 8 := Nat.mod_lt _ (by decide)
    have hodd : q % 2 = 1 := Nat.odd_iff.mp ho
    have hmod : (q ^ 2 - 1) % 8 = (q ^ 2 + 7) % 8 := by omega
    rw [hmod]
    interval_cases he : q % 8 <;> norm_num [Nat.add_mod, Nat.pow_mod, he] <;> omega
  have h2 : 2 ∣ q ^ 3 - 1 := by
    obtain ⟨a, ha⟩ := ho.pow (n := 3)
    change q ^ 3 = 2 * a + 1 at ha
    exact ⟨a, by omega⟩
  have hd : 16 ∣ Nat.card PSL(3,F) * Nat.gcd 3 (q - 1) := by
    rw [psl3_card_gcd]
    simpa only [mul_assoc] using dvd_mul_of_dvd_right (Nat.mul_dvd_mul h2 h8) (q ^ 3)
  exact (show Nat.Coprime 16 (Nat.gcd 3 (q - 1)) from
    (by decide : Nat.Coprime 16 3).of_dvd_right (Nat.gcd_dvd_left _ _)).dvd_of_dvd_mul_right hd

theorem sixteen_dvd_psu3_odd {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {q : ℕ}
    (hq : 1 < q) (ho : Odd q) (hc : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    16 ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have h8 : 8 ∣ q ^ 2 - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hm : q % 8 < 8 := Nat.mod_lt _ (by decide)
    have hodd : q % 2 = 1 := Nat.odd_iff.mp ho
    have hmod : (q ^ 2 - 1) % 8 = (q ^ 2 + 7) % 8 := by omega
    rw [hmod]
    interval_cases he : q % 8 <;> norm_num [Nat.add_mod, Nat.pow_mod, he] <;> omega
  have h2 : 2 ∣ q ^ 3 + 1 := by
    obtain ⟨a, ha⟩ := ho.pow (n := 3)
    exact ⟨a + 1, by omega⟩
  rw [BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective J hc hconj]
  have hd : 16 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    rw [mul_right_comm]
    exact dvd_mul_of_dvd_left (Nat.mul_dvd_mul h2 h8) _
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply (Nat.gcd_dvd_right 3 (q + 1)).trans
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact ⟨q ^ 2 - q + 1, by nlinarith [Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)]⟩
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  exact ((show Nat.Coprime 16 (Nat.gcd 3 (q + 1)) from
    (by decide : Nat.Coprime 16 3).of_dvd_right (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd hg)

theorem psl2_elementary_sylow_card {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (P : Sylow 2 PSL(2,F)) [IsElementaryAbelian 2 P] : Nat.card P = 4 := by
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  let : IsElementaryAbelian 2 (DihedralGroup (2 ^ m)) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hd : 2 ^ m ∣ 2 := by
    rw [← DihedralGroup.orderOf_r_one (n := 2 ^ m)]
    exact (Monoid.order_dvd_exponent (DihedralGroup.r 1)).trans
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := DihedralGroup (2 ^ m)))
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  have he : m = 1 := by
    have hh : 2 ^ m ≤ 2 ^ 1 := hle
    have hb := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, he]
  rfl

theorem psl2_mod_eight_of_elementary_sylow {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (P : Sylow 2 PSL(2,F)) [IsElementaryAbelian 2 P] :
    Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
  have hP := psl2_elementary_sylow_card ho P
  have hnot : ¬8 ∣ Nat.card PSL(2,F) := by
    intro hd
    have hh := P.pow_dvd_card_of_pow_dvd_card (n := 3) hd
    rw [hP] at hh
    norm_num at hh
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := ho
  have hodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice hodd
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have hmod : q % 8 < 8 := Nat.mod_lt _ (by decide)
  have hoddmod : q % 2 = 1 := Nat.odd_iff.mp hodd
  by_contra! he
  have hres : q % 8 = 1 ∨ q % 8 = 7 := by omega
  have hd : 16 ∣ q * (q ^ 2 - 1) := by
    apply Nat.dvd_of_mod_eq_zero
    have hsub : (q ^ 2 - 1) % 16 = (q ^ 2 + 15) % 16 := by omega
    have hm16 : q % 16 < 16 := Nat.mod_lt _ (by decide)
    have hr16 : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
    rcases hr16 with hh | hh | hh | hh <;>
      simp [Nat.mul_mod, hsub, Nat.add_mod, Nat.pow_mod, hh]
  rw [← h] at hd
  obtain ⟨a, ha⟩ := hd
  apply hnot
  exact ⟨a, by omega⟩


end Theory.ClassicalSmallSylow
