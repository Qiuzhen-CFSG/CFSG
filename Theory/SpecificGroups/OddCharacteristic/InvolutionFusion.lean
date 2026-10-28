module

public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.PSL2Center
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL3Three.EvenLocals
public import Theory.SpecificGroups.SL3.InvolutionConjugacy

/-!
# Noncommuting involutions in the odd-characteristic source models

PSL₂(p), for p ≥ 7 with an adjacent power of two, has a dihedral Sylow of
order at least eight. Its two standard reflections do not commute. In the
published semidihedral presentation of a Sylow of SL₃(3), the involutions
b and aba⁻¹ have product a² of order four. Existing matrix fusion theorems
place all involutions in one class. The canonical SL₃(3) to PSL₃(3) map is
an isomorphism; no matrix enumeration is used here.

Source: Aschbacher--Smith 1.1.5(3)(e) and the Bender inspection, pp.519--520.
The PSL₂(5) Sylow four-group is deliberately retained.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory.OddCharacteristicInvolutionFusion

/-- Two noncommuting reflections in a dihedral group with rotation order ≥4. -/
theorem dihedral_pair {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : DihedralGroup n, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b := by
  refine ⟨DihedralGroup.sr 0, DihedralGroup.sr 1,
    DihedralGroup.orderOf_sr _, DihedralGroup.orderOf_sr _, ?_⟩
  intro hc
  have hp : (DihedralGroup.sr (0 : ZMod n) * DihedralGroup.sr 1) ^ 2 = 1 := by
    rw [hc.mul_pow, pow_two, pow_two, DihedralGroup.sr_mul_self,
      DihedralGroup.sr_mul_self, mul_one]
  have hd : n ∣ 2 := by
    have hh := orderOf_dvd_of_pow_eq_one hp
    simpa only [DihedralGroup.sr_mul_sr, sub_zero, DihedralGroup.orderOf_r_one] using hh
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

private theorem eight_dvd_psl2_card {p k : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) :
    8 ∣ Nat.card PSL(2, ZMod p) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hk : 3 ≤ k := by
    by_contra! hh
    interval_cases k <;> norm_num at hpk <;> omega
  have h8 : 8 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have hsub : 2 ∣ p - 1 := by
    obtain ⟨a, ha⟩ := hpodd
    exact ⟨a, by omega⟩
  have hadd : 2 ∣ p + 1 := by
    obtain ⟨a, ha⟩ := hpodd
    exact ⟨a + 1, by omega⟩
  have h16 : 16 ∣ (p - 1) * (p + 1) := by
    rcases hpk with h | h
    · exact Nat.mul_dvd_mul (h ▸ h8) hadd
    · exact Nat.mul_dvd_mul hsub (h ▸ h8)
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
      Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  have hcard := GorensteinWalter.psl2_card_formula (ZMod p)
    ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩
  rw [hcard, Nat.card_zmod, hsq]
  exact Nat.dvd_div_of_mul_dvd (dvd_mul_of_dvd_right h16 p)

/-- The actual prime-field PSL₂ Sylow obstruction outside the four-group case. -/
theorem psl2_pair {p k : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (P : Sylow 2 PSL(2, ZMod p)) :
    ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model
    (ZMod p) ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩ P
  have h8 : 8 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 3)
    (eight_dvd_psl2_card hp7 hpk)
  have hm2 : 2 ≤ m := by
    by_contra! hh
    have hm1 : m = 1 := by omega
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm1] at h8
    norm_num at h8
  obtain ⟨a, b, ha, hb, hab⟩ := dihedral_pair (show 4 ≤ 2 ^ m from
    Nat.pow_le_pow_right (by decide : 0 < 2) hm2)
  exact ⟨e.symm a, e.symm b, (e.symm.orderOf_eq a).trans ha,
    (e.symm.orderOf_eq b).trans hb, fun h => hab (by
      have hh := h.map e.toMonoidHom
      change Commute (e (e.symm a)) (e (e.symm b)) at hh
      simpa only [e.apply_symm_apply] using hh)⟩

/-- The order-sixteen semidihedral presentation contains noncommuting involutions. -/
theorem semidihedral_pair {D : Type*} [Group D] (a b : D)
    (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hrel : b * a * b⁻¹ = a ^ 3) :
    ∃ x y : D, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬Commute x y := by
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb2)
  have hprod : b * (a * b * a⁻¹) = a ^ 2 := by
    calc
      _ = (b * a * b⁻¹) * a⁻¹ := by rw [hbi]; group
      _ = a ^ 3 * a⁻¹ := by rw [hrel]
      _ = a ^ 2 := by group
  refine ⟨b, a * b * a⁻¹, hb, ?_, ?_⟩
  · exact ((MulAut.conj a).orderOf_eq b).trans hb
  · intro hc
    have hysq : (a * b * a⁻¹) ^ 2 = 1 := by
      simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj a) hb2
    have hsq : (a ^ 2) ^ 2 = 1 := by rw [← hprod, hc.mul_pow, hb2, hysq, one_mul]
    have hd : 8 ∣ 4 := by
      rw [← ha, orderOf_dvd_iff_pow_eq_one]
      simpa only [← pow_mul] using hsq
    norm_num at hd

/-- Every actual Sylow two-subgroup of SL₃(3) has the required pair. -/
theorem sl3_three_pair (P : Sylow 2 Matrix.PSL3Three.SL) :
    ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b := by
  obtain ⟨a, b, ha, hb, hrel, _⟩ := Matrix.PSL3Three.sylowTwo_generators_SL P
  exact semidihedral_pair a b ha hb hrel

end Theory.GroupTheory.OddCharacteristicInvolutionFusion
