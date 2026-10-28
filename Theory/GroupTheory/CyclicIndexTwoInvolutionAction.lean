module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Involution actions on a cyclic subgroup of index two

An involution outside a cyclic subgroup of order `2^k` and index two, with
centralizer of order four, acts on the supplied generator by inversion or by
the semidihedral exponent `2^(k-1)-1`. The latter alternative requires `k ≥ 3`.
No ambient p-group or noncentrality hypothesis is needed. This elementary
action calculation is independent of constructing a cyclic complement and is
intended for subsequent dihedral/semidihedral presentation recognition.

For the proof, a cyclic-subgroup element fixed by the involution has order
dividing four. Order four would make its powers the entire centralizer and
put the outside involution in the cyclic subgroup, so every fixed element
squares to one. Index-two normality writes the conjugate generator as `a^r`,
with `r < 2^k`. The product of the generator and its conjugate is fixed, giving
`2^k ∣ 2*(r+1)`. This linear divisibility yields the two stated exponents.
The degenerate exponents `k=0,1,2` are treated explicitly.

Source motivation: Stellmacher, *N-Groups*, Section 11, case (I), and its
reference to Gorenstein, *Finite Groups* (1968), Section 5.4.5. The proof here
uses only elementary order, cyclic-subgroup, and centralizer facts from Mathlib,
not a group-recognition or maximal-class classification theorem.
-/

universe u

private theorem fixed_sq_eq_one
    {G : Type u} [Group G] [Finite G] (subgroup : Subgroup G) (x element : G)
    (hxA : x ∉ subgroup) (hyA : element ∈ subgroup)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4)
    (hyC : element ∈ Subgroup.centralizer ({x} : Set G)) : element ^ 2 = 1 := by
  have hd : orderOf element ∣ 4 :=
    hC ▸ (Subgroup.centralizer {x}).orderOf_dvd_natCard hyC
  have hn : orderOf element ≠ 4 := by
    intro heq
    have hYC : Subgroup.zpowers element = Subgroup.centralizer {x} :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyC)
        (by rw [Nat.card_zpowers, heq, hC])
    apply hxA
    apply (Subgroup.zpowers_le.mpr hyA)
    rw [hYC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hd2 : orderOf element ∣ 2 := by
    have hcases := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf element ∣ 2 ^ 2 by simpa using hd)
    obtain ⟨exponent, he, hr⟩ := hcases
    interval_cases exponent <;> simp_all
  exact orderOf_dvd_iff_pow_eq_one.mp hd2

public theorem involution_conj_eq_inv_or_semidihedral_of_zpowers_index_two
    {G : Type u} [Group G] [Finite G] (a x : G) (k : ℕ)
    (ha : orderOf a = 2 ^ k) (hindex : (Subgroup.zpowers a).index = 2)
    (hxA : x ∉ Subgroup.zpowers a) (hx : orderOf x = 2)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    x * a * x⁻¹ = a⁻¹ ∨
      (3 ≤ k ∧ x * a * x⁻¹ = a ^ (2 ^ (k - 1) - 1)) := by
  classical
  have hx2 : x * x = 1 := by simpa [pow_two, hx] using pow_orderOf_eq_one x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hbA : x * a * x⁻¹ ∈ Subgroup.zpowers a :=
    (Subgroup.normal_of_index_eq_two hindex).conj_mem a (Subgroup.mem_zpowers a) x
  obtain ⟨exponent, hexp, hr⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hbA)
  have hrlt : exponent < 2 ^ k := by simpa [ha] using Finset.mem_range.mp hexp
  have hyC : a * (x * a * x⁻¹) ∈ Subgroup.centralizer ({x} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    symm
    have hcomm : a * (x * a * x⁻¹) = (x * a * x⁻¹) * a := by
      rw [← hr]
      exact (Commute.self_pow a exponent).eq
    calc
      x * (a * (x * a * x⁻¹)) = (x * a * x⁻¹) * (a * x) := by
        rw [hxi]
        group
      _ = (a * (x * a * x⁻¹)) * x := by rw [← mul_assoc, ← hcomm]
  have hy2 := fixed_sq_eq_one (Subgroup.zpowers a) x (a * (x * a * x⁻¹))
    hxA ((Subgroup.zpowers a).mul_mem (Subgroup.mem_zpowers a) hbA) hC hyC
  have hd : 2 ^ k ∣ (exponent + 1) * 2 := by
    rw [← ha, orderOf_dvd_iff_pow_eq_one, pow_mul]
    simpa [pow_succ, ← hr, (Commute.self_pow a exponent).eq] using hy2
  by_cases hk0 : k = 0
  · have ha1 : a = 1 := orderOf_eq_one_iff.mp (by simpa [hk0] using ha)
    simp [ha1]
  have hsplit : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have hdhalf : 2 ^ (k - 1) ∣ exponent + 1 := by
    rw [hsplit] at hd
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp hd
  obtain ⟨factor, hfactor⟩ := hdhalf
  have hpositive : 0 < 2 ^ (k - 1) := by positivity
  have hfactorcases : factor = 1 ∨ factor = 2 := by
    rw [hsplit] at hrlt
    have : factor < 3 := by nlinarith
    have : factor ≠ 0 := by intro hz; simp [hz] at hfactor
    omega
  rcases hfactorcases with hf | hf
  · have hrhalf : exponent = 2 ^ (k - 1) - 1 := by
      rw [hf, mul_one] at hfactor
      omega
    have hk3 : 3 ≤ k := by
      by_contra hsmall
      have hkcases : k = 1 ∨ k = 2 := by omega
      rcases hkcases with rfl | rfl
      · have he0 : exponent = 0 := by simpa using hrhalf
        have hb1 : x * a * x⁻¹ = 1 := by rw [← hr, he0, pow_zero]
        have ha1 : a = 1 := by
          simpa [mul_assoc] using congrArg (fun value => x⁻¹ * value * x) hb1
        simp [ha1] at ha
      · have he1 : exponent = 1 := by simpa using hrhalf
        have hb : x * a * x⁻¹ = a := by rw [← hr, he1, pow_one]
        have haC : a ∈ Subgroup.centralizer ({x} : Set G) := by
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          have hh := congrArg (fun value => value * x) hb
          simpa [mul_assoc] using hh.symm
        have hasq := fixed_sq_eq_one (Subgroup.zpowers a) x a hxA
          (Subgroup.mem_zpowers a) hC haC
        have had := orderOf_dvd_of_pow_eq_one hasq
        rw [ha] at had
        norm_num at had
    exact Or.inr ⟨hk3, by rw [← hr, hrhalf]⟩
  · left
    have hrfull : exponent + 1 = 2 ^ k := by simpa [hf, ← hsplit] using hfactor
    have hp : a ^ exponent * a = 1 := by
      rw [← pow_succ, hrfull, ← ha, pow_orderOf_eq_one]
    exact hr.symm.trans (eq_inv_of_mul_eq_one_left hp)
