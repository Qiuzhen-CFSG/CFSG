module

public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# Quotient covers of prescribed prime-power degree

Every prime-power divisor of a finite abelian group's order is the index of
a subgroup. Applying this to the central kernel of a perfect cover gives a
quotient cover of precisely that degree. In particular, ruling out degree 27
covers suffices even when the original kernel has other prime divisors.

The subgroup construction iterates the finite nilpotent prime-index theorem.
The quotient is by a subgroup of the literal kernel, so its projection to the
base group is unchanged. This is the reduction used for the three-primary
part of Aschbacher--Smith I.1.4(5), printed p.408, and GLS3 §6.1.
No family-specific multiplier calculation is asserted here.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace PerfectCentralCovering

/-- Every prime-power divisor of a finite abelian order occurs as an index. -/
theorem exists_subgroup_index_prime_pow
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    {p : ℕ} [Fact p.Prime] (n : ℕ) (hd : p ^ n ∣ Nat.card A) :
    ∃ N : Subgroup A, N.index = p ^ n := by
  induction n generalizing A with
  | zero => exact ⟨⊤, by simp⟩
  | succ n ih =>
    have hp : p ∣ Nat.card A := (dvd_pow_self p (by omega : n + 1 ≠ 0)).trans hd
    have hex : ∃ N : Subgroup A, N.Normal ∧ N.index = p := by
      by_contra h
      apply Group.not_dvd_card_of_nilpotent_of_no_normal_index_prime ?_ hp
      intro N hN hi
      exact h ⟨N, hN, hi⟩
    obtain ⟨N, _, hi⟩ := hex
    have hcard : Nat.card N * p = Nat.card A := by simpa [hi] using N.card_mul_index
    have hdN : p ^ n ∣ Nat.card N := by
      rw [← hcard, pow_succ] at hd
      exact (Nat.mul_dvd_mul_iff_right (Fact.out : p.Prime).pos).mp hd
    obtain ⟨D, hD⟩ := ih hdN
    refine ⟨D.map N.subtype, ?_⟩
    rw [index_map_subtype, hD, hi, pow_succ]

universe u v
variable {E : Type u} {G : Type v} [Group E] [Finite E] [Group G] [Finite G]

/-- A prime-power divisor survives in a quotient cover with exactly that degree. -/
theorem Cover.exists_primePower_kernel_quotient (c : Cover E G)
    {p : ℕ} [Fact p.Prime] (n : ℕ) (hp : p ^ n ∣ Nat.card c.toMonoidHom.ker) :
    ∃ (D : Subgroup E) (_hDn : D.Normal) (hD : D ≤ c.toMonoidHom.ker),
      Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker = p ^ n := by
  let : IsMulCommutative c.toMonoidHom.ker := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (c.ker_le_center x.property) y).symm⟩⟩
  obtain ⟨N, hN⟩ := exists_subgroup_index_prime_pow n hp
  let D := N.map c.toMonoidHom.ker.subtype
  have hD : D ≤ c.toMonoidHom.ker := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hDc : D ≤ center E := hD.trans c.ker_le_center
  let hDn : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hDc hx) g, mul_inv_cancel_right]
    exact hx⟩
  refine ⟨D, hDn, hD, ?_⟩
  have hcard : Nat.card c.toMonoidHom.ker = Nat.card D * p ^ n := by
    rw [show Nat.card D = Nat.card N from
      Subgroup.card_map_of_injective c.toMonoidHom.ker.subtype_injective]
    simpa only [hN] using N.card_mul_index.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D))
    ((c.card_kernel_quotientKernelSubgroup D hD).symm.trans hcard)

/-- Exclusion of one exact degree controls arbitrary mixed-prime kernels. -/
theorem Cover.not_primePower_dvd_card_kernel_of_no_primePower_kernel
    (c : Cover E G) {p : ℕ} [Fact p.Prime] (n : ℕ)
    (hno : ∀ (F : Type u) [Group F] [Finite F] (d : Cover F G),
      Nat.card d.toMonoidHom.ker ≠ p ^ n) :
    ¬ p ^ n ∣ Nat.card c.toMonoidHom.ker := by
  intro hp
  obtain ⟨D, hDn, hD, hc⟩ := c.exists_primePower_kernel_quotient n hp
  let : D.Normal := hDn
  exact hno (E ⧸ D) (c.quotientKernelSubgroup D hD) hc

end PerfectCentralCovering
