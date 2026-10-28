module

public import ABG.ChapterII.Section2.FullSylowShapes
public import ABG.ChapterII.Section1.Center
public import Theory.GroupTheory.WreathedThirtyTwo

/-!
# The field sign from a four-element Sylow center

The wrong field sign makes a full GL₂ or GU₂ Sylow semidihedral, with
center of order two. An actual four-element center therefore forces the
linear sign one or the unitary sign three modulo four. The GU₂ proof
uses its determinant-sign level and transports the concrete presentation.

Source: ABG II.2 Lemma 1, article p.17; Aschbacher--Smith A.3.21(b)
and the Sylow-shape step of F.6.18, printed pp.55 and 310.
-/

public section
open Subgroup Matrix.GeneralLinearGroup
namespace Theory.ClassicalSmallSylow

theorem gl2_sylow_mod_four_of_center_four
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (P : Sylow 2 (GL (Fin 2) F)) (hc : Nat.card (center P) = 4) : Nat.card F % 4 = 1 := by
  have hm : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have := Nat.odd_iff.mp ho
    omega
  rcases hm with hm | hm
  · exact hm
  · obtain ⟨S, n, hn, hS, a, b, ha, hb, hab, hgen, _⟩ :=
      Matrix.GeneralLinearGroup.exists_semidihedral_sylow F hm
    have hs : Stellmacher.IsSemidihedralGroup S := ⟨n, hn, hS, a, b, ha, hb, hab, hgen⟩
    have hh := ABG.QuasiDihedral.card_center (ABG.semidihedral_equiv (S.equiv P) hs)
    omega

theorem gu2_sylow_mod_four_of_center_four
    (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (P : Sylow 2 (ABG.GU2 p 1 (by decide)))
    (hc : Nat.card (center P) = 4) : p % 4 = 3 := by
  have hp := (Fact.out : p.Prime).one_lt
  have hm : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp ho
    omega
  rcases hm with hm | hm
  swap
  · exact hm
  have h4 : 4 ∣ p - 1 := by omega
  obtain ⟨n, d, hd, he⟩ := Nat.exists_eq_two_pow_mul_odd (show p - 1 ≠ 0 by omega)
  have hn : 2 ≤ n := by
    by_contra hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul] at he <;>
      have := Nat.odd_iff.mp hd <;> omega
  have hdiv : 2 ^ n ∣ p ^ 1 - 1 := by simpa only [pow_one] using (show 2 ^ n ∣ p - 1 from ⟨d, he⟩)
  have hodd : Odd ((p ^ 1 - 1) / 2 ^ n) := by
    simp only [pow_one]
    rw [he, Nat.mul_div_cancel_left _ (by positivity)]
    exact hd
  obtain ⟨Q, _, hQ, _⟩ := ABG.SU2Level_semidihedral_sylow p 1 ho (by decide) n hn hdiv hodd
  have hP : (P : Subgroup (ABG.GU2 p 1 (by decide))) ≤ ABG.SU2Level p 1 (by decide) 1 := by
    intro a ha
    rw [ABG.mem_SU2Level_iff_orderOf_dvd, pow_one]
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_orderOf_dvd_pow (⟨a, ha⟩ : P)
    let detU := (Matrix.GeneralLinearGroup.det (n := Fin 2)
      (R := GaloisField p (2 * 1))).comp (ABG.unitaryForm 2 p 1 (by decide)).unitarySubgroup.subtype
    have hod : orderOf (det a.val) ∣ 2 ^ k :=
      (orderOf_map_dvd detU a).trans (by simpa using hk)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
    rw [hj]
    by_cases hj1 : j ≤ 1
    · simpa using Nat.pow_dvd_pow 2 hj1
    · have hplus : 4 ∣ p ^ 1 + 1 :=
        (show 4 ∣ 2 ^ j by simpa using Nat.pow_dvd_pow 2 (by omega : 2 ≤ j)).trans
          (hj ▸ ABG.GU2_det_orderOf_dvd p 1 (by decide) a)
      simp only [pow_one] at hplus
      omega
  let e : P ≃* Q := (Subgroup.subgroupOfEquivOfLe hP).symm.trans ((P.subtype hP).equiv Q)
  have hh := ABG.QuasiDihedral.card_center (ABG.semidihedral_equiv e.symm hQ)
  omega

end Theory.ClassicalSmallSylow
