module

public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Cubic kernel images in an order-nine core quotient

Suppose A/O₂(A) has order nine and A acts in a finite group B whose order
has greatest common divisor three with nine. A two-perfect subgroup acting
nontrivially forces the kernel's image in A/O₂(A) to have order three.
Indeed, the index of ker(f)O₂(A) divides both orders. Index one would make
the two-perfect subgroup act through a two-group, so this index is three.

This does not require O₂(A) to lie in the action kernel.
Source application: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

public section
open Subgroup

namespace MonoidHom

/-- A nontrivial two-perfect action forces the literal kernel image to be cubic. -/
theorem card_kernel_image_cubic
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (P : Subgroup A) (hP : IsPPerfect 2 P)
    (hout : ¬ P ≤ f.ker) (h9 : Nat.card (A ⧸ pCore 2 A) = 9)
    (hB : Nat.gcd 9 (Nat.card B) = 3) :
    Nat.card (f.ker.map (QuotientGroup.mk' (pCore 2 A))) = 3 := by
  let N := f.ker ⊔ pCore 2 A
  have hN9 : N.index ∣ 9 := by
    rw [← h9, ← index_eq_card]
    exact index_dvd_of_le (show pCore 2 A ≤ N from le_sup_right)
  have hNB : N.index ∣ Nat.card B := by
    have hNk : N.index ∣ f.ker.index := index_dvd_of_le le_sup_left
    rw [index_ker] at hNk
    exact hNk.trans (card_subgroup_dvd_card f.range)
  have hN3 : N.index ∣ 3 := hB ▸ Nat.dvd_gcd hN9 hNB
  have hNi : N.index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hN3 with h1 | h3
    · have htop : N = ⊤ := index_eq_one.mp h1
      exact (hout (le_normal_of_isPPerfect_of_le_sup_pGroup P f.ker (pCore 2 A)
        hP pCore_isPGroup (by change P ≤ N; rw [htop]; exact le_top))).elim
    · exact h3
  have hi : (f.ker.map (QuotientGroup.mk' (pCore 2 A))).index = 3 := by
    rw [index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' (pCore 2 A)).range_eq_top_of_surjective
        (QuotientGroup.mk'_surjective _), index_top, mul_one]
    exact hNi
  have hc := (f.ker.map (QuotientGroup.mk' (pCore 2 A))).index_mul_card
  rw [hi, h9] at hc
  omega

end MonoidHom
