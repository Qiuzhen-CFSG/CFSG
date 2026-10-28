module
public import Theory.GroupTheory.FrattiniFixedFreeDisplacement
public import Theory.GroupTheory.PGroup.ClassTwoOmegaGenerated
public import Theory.Frattini.PGroup

/-!
# Fixed Frattini subgroups and inversion on the Frattini quotient

Let an involutory automorphism of an odd p-group fix its Frattini subgroup
pointwise and invert the Frattini quotient. Its displacements centralize the
Frattini subgroup and generate the whole group, so the group has class at most
two. Each displacement is inverted, while its p-th power is fixed; odd order
forces that power to be trivial. First-omega generation and the class-two
collection formula now give exponent dividing p.

Source application: Aschbacher–Smith, construction before 12.2.22, printed
pp.802–803, supplying the class and exponent hypotheses of A.1.24 (p.25).
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace MulAut
variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- Fixation of Frattini and inversion modulo Frattini force class at most
two and exponent dividing the odd prime. -/
theorem class_two_exponent_of_fixed_frattini_inversion
    (hP : IsPGroup p P) (hp : Odd p) (a : MulAut P)
    (ha : Function.Involutive a)
    (hfix : ∀ z ∈ frattini P, a z = z)
    (hinv : ∀ x : P, a x * x ∈ frattini P) :
    _root_.commutator P ≤ center P ∧ Monoid.exponent P ∣ p := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact hp.pow
  have hqinv (x : P ⧸ frattini P) : quotientAut (frattini P) a x = x⁻¹ := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    rw [quotientAut_apply_mk]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hinv x)
  have hqfix (x : P ⧸ frattini P) (hx : quotientAut (frattini P) a x = x) : x = 1 := by
    have he : x = x⁻¹ := hx.symm.trans (hqinv x)
    have h2 : x ^ 2 = 1 := by rw [pow_two, ← mul_inv_cancel x]; exact congrArg (x * ·) he
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hodd.of_dvd_nat (card_quotient_dvd_card (frattini P))).coprime_two_right
      (orderOf_dvd_natCard x) (orderOf_dvd_of_pow_eq_one h2))
  have hC : centralizer (frattini P : Set P) = ⊤ := by
    apply eq_top_of_fixedFree_quotient_displacements (frattini P) le_rfl a hqfix
    intro x z hz
    have hz' : x⁻¹ * z * x ∈ frattini P := by
      simpa only [inv_inv] using (inferInstance : (frattini P).Normal).conj_mem z hz x⁻¹
    have he := hfix _ hz'
    rw [map_mul, map_mul, map_inv, hfix z hz] at he
    calc
      z * (a x * x⁻¹) = a x * ((a x)⁻¹ * z * a x) * x⁻¹ := by group
      _ = a x * (x⁻¹ * z * x) * x⁻¹ := by rw [he]
      _ = (a x * x⁻¹) * z := by group
  have hphi : frattini P ≤ center P := centralizer_eq_top_iff_subset.mp hC
  have hclass : _root_.commutator P ≤ center P :=
    (commutator_le_frattini_of_isPGroup (p := p)).trans hphi
  have hOmega : omega₁ P (p := p) = ⊤ := by
    apply eq_top_of_fixedFree_quotient_displacements (frattini P) le_rfl a hqfix
    intro x
    let y := a x * x⁻¹
    have hai : a y = y⁻¹ := by simp only [y, map_mul, map_inv, ha x, mul_inv_rev, inv_inv]
    have hf : a (y ^ p) = y ^ p := hfix _ (pth_power_mem_frattini_of_isPGroup (p := p) y)
    have hi : y ^ p = (y ^ p)⁻¹ := by
      rw [map_pow, hai, inv_pow] at hf
      exact hf.symm
    have h2 : (y ^ p) ^ 2 = 1 := by
      calc (y ^ p) ^ 2 = y ^ p * (y ^ p)⁻¹ := by rw [pow_two]; exact congrArg (y ^ p * ·) hi
           _ = 1 := mul_inv_cancel _
    have hyp : y ^ p = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      hodd.coprime_two_right (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one h2))
    apply Subgroup.subset_closure
    change y ^ (p ^ 1) = 1
    simpa only [pow_one] using hyp
  exact ⟨hclass, exponent_dvd_prime_of_omega_one_eq_top
    (fun h => hp.not_two_dvd_nat (by rw [h])) hclass hOmega⟩
end MulAut
