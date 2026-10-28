module

public import Theory.GroupTheory.PerfectCentralCoverSylowNine
public import Theory.PGroupCore
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Odd parts of kernels of finite perfect central covers

Cyclic Sylow transfer excludes a prime from a perfect central kernel when
its square does not divide the order downstairs. If the three-part downstairs
has order at most nine, the order-nine kernel theorem bounds the three-part
of the kernel by three. Together these give an actual divisibility by a
power of two times three. Trivial two-core upstairs removes the two-part.

These are the cover deductions used for PSL₃(4), M₂₂ and J₁ in
Aschbacher–Smith A.3.6 and A.3.8, printed pp.43–46; the covering and
cyclic-Sylow conventions are I.1.1–I.1.2, printed p.407.
-/

public section
open Subgroup
namespace PerfectCentralCovering

variable {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]

/-- A squarefree prime factor downstairs cannot occur in a perfect central kernel. -/
theorem Cover.not_dvd_card_kernel_of_square_not_dvd
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (hsq : ¬ p ^ 2 ∣ Nat.card G) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_dvd_card_multiplier_of_isCyclic_sylow
  intro Q
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hnle : n ≤ 1 := by
    by_contra h
    apply hsq
    exact (pow_dvd_pow p (by omega : 2 ≤ n)).trans
      (hn ▸ (Q : Subgroup G).card_subgroup_dvd_card)
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa using pow_dvd_pow p hnle

/-- The order-nine result also covers a smaller three-part downstairs. -/
theorem Cover.not_nine_dvd_card_kernel_of_cube_not_dvd
    (f : Cover E G) (hcube : ¬ 27 ∣ Nat.card G) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 G := default
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hnle : n ≤ 2 := by
    by_contra h
    apply hcube
    exact (pow_dvd_pow 3 (by omega : 3 ≤ n)).trans
      (hn ▸ (Q : Subgroup G).card_subgroup_dvd_card)
  by_cases hn2 : n = 2
  · exact f.not_nine_dvd_card_kernel_of_sylow_nine Q (by simpa [hn2] using hn)
  · have hQcyc : IsCyclic Q := by
      apply isCyclic_of_card_dvd_prime (p := 3)
      rw [hn]
      simpa using pow_dvd_pow 3 (by omega : n ≤ 1)
    have hnot := f.not_dvd_card_multiplier_of_isCyclic_sylow (p := 3)
      (fun Q' => (MulEquiv.isCyclic (Sylow.equiv Q' Q)).mpr hQcyc)
    exact fun h => hnot (dvd_trans (by norm_num : 3 ∣ 9) h)

/-- Only one factor of three can remain in the odd part of the kernel.
This is divisibility, not a numerical upper bound. -/
theorem Cover.kernel_card_dvd_two_pow_mul_three
    (f : Cover E G) (hcube : ¬ 27 ∣ Nat.card G)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ Nat.card G) :
    ∃ n : ℕ, Nat.card f.toMonoidHom.ker ∣ 2 ^ n * 3 := by
  let m := Nat.card f.toMonoidHom.ker
  have hm : m ≠ 0 := Nat.card_pos.ne'
  have h9 := f.not_nine_dvd_card_kernel_of_cube_not_dvd hcube
  refine ⟨m.factorization 2, (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr ?_⟩
  intro p k hp hk
  by_cases hp2 : p = 2
  · subst p
    exact (pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization hm).mp hk)).trans
      (dvd_mul_right _ _)
  by_cases hp3 : p = 3
  · subst p
    have hk1 : k ≤ 1 := by
      by_contra h
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hk)
    exact (show 3 ^ k ∣ 3 by simpa using pow_dvd_pow 3 hk1).trans (dvd_mul_left 3 _)
  · have hk0 : k = 0 := by
      by_contra hk0
      let : Fact p.Prime := ⟨hp⟩
      apply f.not_dvd_card_kernel_of_square_not_dvd (hsq p hp hp2 hp3)
      exact (show p ∣ p ^ k by simpa using pow_dvd_pow p (by omega : 1 ≤ k)).trans hk
    simp [hk0]

private theorem not_dvd_card_central_of_pCore_eq_bot
    {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (hN : N ≤ center H) (p : ℕ) [Fact p.Prime]
    (hcore : pCore p H = ⊥) : ¬ p ∣ Nat.card N := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) p hd
  let Z := (zpowers z).map N.subtype
  have hZc : Z ≤ center H := (map_subtype_le _).trans hN
  let : Z.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hZc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    simp only [Z, card_map_of_injective N.subtype_injective,
      Nat.card_zpowers, hz, pow_one]
  have hle : Z ≤ pCore p H := le_sSup ⟨inferInstance, hZp⟩
  have hz1 : (z : H) = 1 := (hcore ▸ hle) (mem_map_of_mem _ (mem_zpowers z))
  have hz' : z = 1 := Subtype.ext hz1
  exact (Fact.out : p.Prime).ne_one (by simpa [hz'] using hz.symm)

/-- The source's trivial two-core removes the kernel's entire two-part. -/
theorem Cover.kernel_card_dvd_three_of_pCore_eq_bot
    (f : Cover E G) (hcore : pCore 2 E = ⊥) (hcube : ¬ 27 ∣ Nat.card G)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ Nat.card G) :
    Nat.card f.toMonoidHom.ker ∣ 3 := by
  obtain ⟨n, hn⟩ := f.kernel_card_dvd_two_pow_mul_three hcube hsq
  have hnot := not_dvd_card_central_of_pCore_eq_bot f.toMonoidHom.ker
    f.ker_le_center 2 hcore
  have hc : Nat.Coprime (Nat.card f.toMonoidHom.ker) (2 ^ n) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hnot).symm).pow_right n
  exact hc.dvd_of_dvd_mul_left hn

/-- Squarefree odd part downstairs and trivial two-core upstairs make the
given perfect central covering map injective. -/
theorem Cover.injective_of_squarefree_odd_part_of_pCore_eq_bot
    (f : Cover E G) (hcore : pCore 2 E = ⊥)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card G) :
    Function.Injective f.toMonoidHom := by
  apply f.toMonoidHom.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  by_contra h
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    exact not_dvd_card_central_of_pCore_eq_bot f.toMonoidHom.ker
      f.ker_le_center 2 hcore hd
  · exact f.not_dvd_card_kernel_of_square_not_dvd (hsq p hp hp2) hd

end PerfectCentralCovering
