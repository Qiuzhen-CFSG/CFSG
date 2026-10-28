module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryBounds

/-!
# Arithmetic reduction for a marked linear--unitary octagon pair

The marked octagon supplies opposite degree parity and the two numerical
inequalities. Once the Cartan argument supplies
`Odd a → 2^a - 1 ∣ 2^(2*b) - 1` and `2^b - 1 ∣ 2^a - 1`, the remaining
degree calculation is elementary: the first divisibility excludes odd `a`,
the second gives `b ∣ a`, and the upper bound leaves the ratios
`2`, `4`, and `6`.

The two divisibilities are explicit premises because their unitary torus
transport depends on the scalar convention and on the regular-cover adapter.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

private theorem degree_dvd {a b : ℕ} (h : 2^a - 1 ∣ 2^b - 1) : a ∣ b := by
  have he := Nat.mod_eq_zero_of_dvd h
  rw [Nat.pow_sub_one_mod_pow_sub_one] at he
  have hh : 2^(b % a) ≤ 2^0 := by omega
  have hz := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  exact Nat.dvd_of_mod_eq_zero (by omega)

/-- The lower octagon bound excludes odd linear degree once its perpendicular
Cartan image divides the unitary field-unit order. -/
theorem linear_unitary_degree_parity_of_odd_divisibility
    {a b : ℕ} (hb : 0 < b) (hpar : a % 2 ≠ b % 2) (hlower : 3 * b ≤ 2 * a)
    (hleft : Odd a → 2^a - 1 ∣ 2^(2*b) - 1) : Even a ∧ Odd b := by
  have hev : Even a := by
    by_contra hna
    have hoa : Odd a := Nat.not_even_iff_odd.mp hna
    have hdivleft : a ∣ 2*b := degree_dvd (hleft hoa)
    have hdivab : a ∣ b := hoa.coprime_two_right.dvd_mul_left.mp (by
      simpa [Nat.mul_comm] using hdivleft)
    obtain ⟨k, hk⟩ := hdivab
    have hkpos : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := by omega
      simp [hkz] at hk
      omega
    have hkle : 3*k ≤ 2 := by
      rw [hk] at hlower
      nlinarith [hoa.pos]
    omega
  have hob : Odd b := by
    have hbn : ¬ Even b := by
      intro hbEven
      apply hpar
      exact (Nat.even_iff.mp hev).trans (Nat.even_iff.mp hbEven).symm
    exact Nat.not_even_iff_odd.mp hbn
  exact ⟨hev,hob⟩

/-- The degree reduction requires the first Cartan divisibility only in the
odd linear-degree branch, where the perpendicular reflection centralizes the
linear root. The second divisibility then leaves ratios two, four and six. -/
theorem linear_unitary_degree_reduction_of_odd_divisibility
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpar : a % 2 ≠ b % 2) (hupper : a ≤ 6 * b) (hlower : 3 * b ≤ 2 * a)
    (hleft : Odd a → 2^a - 1 ∣ 2^(2*b) - 1)
    (hright : 2^b - 1 ∣ 2^a - 1) :
    Even a ∧ Odd b ∧ (a = 2*b ∨ a = 4*b ∨ a = 6*b) := by
  have hdivright : b ∣ a := degree_dvd hright
  obtain ⟨hev,hob⟩ := linear_unitary_degree_parity_of_odd_divisibility hb hpar hlower hleft
  obtain ⟨k, hk⟩ := hdivright
  have hkbound : k ≤ 6 := by
    rw [hk] at hupper
    exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hupper) hb
  have hkEven : Even k := by
    by_contra hke
    have hko : Odd k := Nat.not_even_iff_odd.mp hke
    have hodd : Odd (k*b) := hko.mul hob
    have hodd' : Odd a := by simpa [hk, Nat.mul_comm] using hodd
    exact (Nat.not_odd_iff_even.mpr hev) hodd'
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    simp [hkz] at hk
    omega
  obtain ⟨t, ht⟩ := hkEven
  have hkcases : k = 2 ∨ k = 4 ∨ k = 6 := by omega
  rcases hkcases with h2 | h4 | h6
  · exact ⟨hev, hob, Or.inl (by simpa [h2, Nat.mul_comm] using hk)⟩
  · exact ⟨hev, hob, Or.inr (Or.inl (by simpa [h4, Nat.mul_comm] using hk))⟩
  · exact ⟨hev, hob, Or.inr (Or.inr (by simpa [h6, Nat.mul_comm] using hk))⟩

/-- The degree reduction when both Cartan divisibilities are supplied. -/
theorem linear_unitary_degree_reduction
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpar : a % 2 ≠ b % 2) (hupper : a ≤ 6 * b) (hlower : 3 * b ≤ 2 * a)
    (hleft : 2^a - 1 ∣ 2^(2*b) - 1)
    (hright : 2^b - 1 ∣ 2^a - 1) :
    Even a ∧ Odd b ∧ (a = 2*b ∨ a = 4*b ∨ a = 6*b) :=
  linear_unitary_degree_reduction_of_odd_divisibility ha hb hpar hupper hlower
    (fun _ => hleft) hright

private theorem dvd_of_projective_unitary_cartan
    {a b : ℕ} (hleft :
      2^a - 1 ∣ (2^(2*b) - 1) / Nat.gcd 3 (2^b + 1)) : 2^a - 1 ∣ 2^(2*b) - 1 := by
  let d := Nat.gcd 3 (2^b + 1)
  have hd : d ∣ 2^(2*b) - 1 := by
    apply dvd_trans (Nat.gcd_dvd_right 3 (2^b + 1))
    have he : 2^(2*b) - 1 = (2^b - 1) * (2^b + 1) := by
      rw [show 2*b = b+b by omega, pow_add]
      simpa [mul_comm] using (mul_self_tsub_one (2^b))
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_refl _) _
  have hmul : 2^a - 1 ∣ ((2^(2*b) - 1) / d) * d :=
    dvd_mul_of_dvd_left hleft d
  have hfull : 2^a - 1 ∣ 2^(2*b) - 1 := by
    simpa only [Nat.div_mul_cancel hd] using hmul
  exact hfull

/-- The same reduction with the stronger projective-unitary torus premise.
Divisibility of the quotient order implies divisibility of the full order. -/
theorem linear_unitary_degree_reduction_projective
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpar : a % 2 ≠ b % 2) (hupper : a ≤ 6 * b) (hlower : 3 * b ≤ 2 * a)
    (hleft : 2^a - 1 ∣ (2^(2*b) - 1) / Nat.gcd 3 (2^b + 1))
    (hright : 2^b - 1 ∣ 2^a - 1) :
    Even a ∧ Odd b ∧ (a = 2*b ∨ a = 4*b ∨ a = 6*b) :=
  linear_unitary_degree_reduction ha hb hpar hupper hlower
    (dvd_of_projective_unitary_cartan hleft) hright

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
