module

public import Theory.GroupTheory.PGroup.NoNormalFour

/-!
# Involution actions without normal four-groups

An involution outside a cyclic normal self-centralizing subgroup of a finite
two-group without normal four-groups fixes only elements of order at most two
in that subgroup. If the cyclic subgroup has index two, the involution therefore
has centralizer of order four and gives the dihedral/semidihedral alternative.

The action exponent is odd. An exponent congruent to one modulo four would
be the modular twist, which produces a normal four-group. The exponent is
therefore three modulo four, and cancellation of its odd factor bounds the
fixed subgroup. This is an elementary part of GLS, Number 2, Chapter C,
Lemma 10.11, using the modular-action argument in `CyclicSelfCentralizerFour`.
-/

open Subgroup

/-- A nonidentity square root of one modulo a power of two that is one modulo
four is the modular exponent. -/
public theorem Nat.eq_one_add_two_pow_of_mod_four
    (n r : ℕ) (hn : 3 ≤ n) (hrlt : r < 2 ^ n) (hr4 : r % 4 = 1)
    (hr1 : r ≠ 1) (hrr : 2 ^ n ∣ r * r - 1) :
    r = 1 + 2 ^ (n - 1) := by
  have hrlower : 1 ≤ r := by omega
  have hrprod : 2 ^ n ∣ (r - 1) * (r + 1) := by
    convert hrr using 1
    have ht : r - 1 + 1 = r := by omega
    have ht2 : r * r - 1 + 1 = r * r := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hrhalf : 2 ^ (n - 1) ∣ r - 1 := by
    have hrplus : r + 1 = 2 * (r / 2 + 1) := by omega
    have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hsplit, hrplus, ← mul_assoc, mul_right_comm] at hrprod
    have hdiv := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp hrprod
    have hodd : Nat.Coprime 2 (r / 2 + 1) := Nat.coprime_two_left.mpr (by
      exact ⟨r / 4, by omega⟩)
    exact (hodd.pow_left (n - 1)).dvd_mul_right.mp hdiv
  obtain ⟨k, hk⟩ := hrhalf
  have hhalfpos : 0 < 2 ^ (n - 1) := by positivity
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hk1 : k = 1 := by
    rw [hsplit] at hrlt
    have hrminus : r - 1 + 1 = r := by omega
    have hkpos : 0 < k := by
      by_contra h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    nlinarith
  rw [hk1, mul_one] at hk
  omega

namespace IsPGroup

/-- Without a normal four-group, an outer involution acts on a cyclic normal
self-centralizing subgroup with exponent three modulo four. -/
public theorem involution_action_mod_four_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A)
    (a e : P) (n r : ℕ) (hA : A = zpowers a) (ha : orderOf a = 2 ^ n)
    (he : e ^ 2 = 1) (heA : e ∉ A)
    (hrlt : r < 2 ^ n) (hact : e * a * e⁻¹ = a ^ r) : r % 4 = 3 := by
  have hr1 : r ≠ 1 := by
    intro hh
    apply heA
    apply hC
    intro y hy
    rw [hA] at hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute a e := by
      have hh' : e * a * e⁻¹ = a := by simpa [hh] using hact
      exact (mul_inv_eq_iff_eq_mul.mp hh').symm
    exact (hc.zpow_left k).eq
  have hp : a ^ (r * r) = a := by
    calc
      a ^ (r * r) = MulAut.conj e (a ^ r) := by
        rw [map_pow, MulAut.conj_apply, hact, pow_mul]
      _ = MulAut.conj e (MulAut.conj e a) := by congr 1; exact hact.symm
      _ = a := by
        have hee : e * e = 1 := by simpa [pow_two] using he
        simp only [MulAut.conj_apply]
        calc
          e * (e * a * e⁻¹) * e⁻¹ = (e * e) * a * (e * e)⁻¹ := by group
          _ = a := by rw [hee]; simp
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have ha1 : a = 1 := orderOf_eq_one_iff.mp (by simpa [hn0] using ha)
    have heC : e ∈ centralizer (A : Set P) := by
      rw [hA, ha1]
      intro x hx
      have hx1 : x = 1 := by simpa using hx
      simp [hx1]
    exact heA (hC heC)
  have hmod : Nat.ModEq (2 ^ n) (r * r) 1 := by
    simpa [ha] using pow_eq_pow_iff_modEq.mp (hp.trans (pow_one a).symm)
  have hr2 : r % 2 = 1 := by
    have hh := hmod.of_dvd (dvd_pow_self 2 (by omega : n ≠ 0))
    have hh' : (r % 2) * (r % 2) % 2 = 1 := by
      simpa [Nat.ModEq, Nat.mul_mod] using hh
    by_cases hh0 : r % 2 = 0
    · simp [hh0] at hh'
    · omega
  have hrpos : 1 ≤ r := by omega
  have hrr : 2 ^ n ∣ r * r - 1 :=
    (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ r * r)).mp hmod.symm
  have hr4 : r % 4 = 1 ∨ r % 4 = 3 := by omega
  rcases hr4 with hr4 | hr4
  · have hn3 : 3 ≤ n := by
      by_contra h
      have hnlt : n < 3 := by omega
      interval_cases n <;> norm_num at hrlt <;> omega
    have hr := Nat.eq_one_add_two_pow_of_mod_four n r hn3 hrlt hr4 hr1 hrr
    exact (hno (hP.exists_normal_four_of_twist A hC a e n hn3 hA ha he heA
      (by simpa [hr] using hact))).elim
  · exact hr4

/-- An outer involution fixes only elements of order at most two in a cyclic
normal self-centralizing subgroup, when no normal four-group exists. -/
public theorem fixed_sq_eq_one_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A)
    (e : P) (he : e ^ 2 = 1) (heA : e ∉ A)
    (d : P) (hd : d ∈ A) (hde : Commute d e) : d ^ 2 = 1 := by
  classical
  obtain ⟨a, haA⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨n, hn⟩ := (hP.to_subgroup A).exists_card_eq
  have ha : orderOf a = 2 ^ n := by rw [← Nat.card_zpowers, haA, hn]
  have hactA : e * a * e⁻¹ ∈ zpowers a := by
    rw [haA]
    exact Normal.conj_mem inferInstance a (haA ▸ mem_zpowers a) e
  obtain ⟨r, hr, hact⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hactA)
  have hrlt : r < 2 ^ n := by simpa [ha] using Finset.mem_range.mp hr
  have hr4 := hP.involution_action_mod_four_of_no_normal_four hno A hC
    a e n r haA.symm ha he heA hrlt hact.symm
  have hdpow : d ^ (r - 1) = 1 := by
    have heq : d ^ r = d := by
      rw [← haA] at hd
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hd)
      calc
        (a ^ k) ^ r = (a ^ r) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = MulAut.conj e (a ^ k) := by rw [map_pow, MulAut.conj_apply, hact]
        _ = a ^ k := mul_inv_eq_iff_eq_mul.mpr hde.eq.symm
    apply mul_right_cancel (b := d)
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r), heq]
  have hodd : Nat.Coprime 2 ((r - 1) / 2) := Nat.coprime_two_left.mpr
    ⟨r / 4, by omega⟩
  apply (hP.powEquiv hodd).injective
  simp only [IsPGroup.powEquiv_apply, one_pow, ← pow_mul]
  convert hdpow using 1
  congr 1
  omega

end IsPGroup
