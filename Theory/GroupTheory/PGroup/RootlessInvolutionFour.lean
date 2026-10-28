module

public import Theory.GroupTheory.PGroup.InvolutionFour

/-!
# Rootless involutions in elementary four-groups

In a finite two-group of order greater than two, an involution with no square
root lies in an elementary four. If no four exists, the unique involution
argument and induction on element orders show that a rootless involution
forces the whole group to have order two.

This is the elementary observation used for the diagonal quotient in
Aschbacher, *On finite groups of component type* (1975), Lemma 3.4, p.95.
The proof uses the central-involution argument, without classifying
cyclic or generalized quaternion groups.
-/

open Subgroup
namespace IsPGroup

/-- A rootless involution in a finite two-group of order greater than two
has a distinct commuting involution, so the two generate a Klein four. -/
public theorem exists_commuting_involution_of_rootless {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcard : 2 < Nat.card P) (x : P)
    (hx : orderOf x = 2) (hroot : ∀ y : P, y ^ 2 ≠ x) :
    ∃ y : P, orderOf y = 2 ∧ x ≠ y ∧ Commute x y := by
  classical
  have hxne : x ≠ 1 := by intro he; simp [he] at hx
  let : Nontrivial P := ⟨⟨x, 1, hxne⟩⟩
  have hfour : ∃ A : Subgroup P, IsElementaryAbelian 2 A ∧ Nat.card A = 4 := by
    by_contra hn
    have hn' : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A ≠ 4 := by
      intro A hA hc
      exact hn ⟨A, hA, hc⟩
    obtain ⟨z, hz, _, huniq⟩ := hP.exists_central_involution_of_no_elementary_four hn'
    have hxz : x = z := (huniq x (by rw [← hx]; exact pow_orderOf_eq_one x)).resolve_left hxne
    have hall (n : ℕ) : ∀ y : P, y ^ (2 ^ n) = 1 → y = 1 ∨ y = z := by
      induction n with
      | zero => intro y hy; exact Or.inl (by simpa using hy)
      | succ n ih =>
        intro y hy
        have hh : (y ^ 2) ^ (2 ^ n) = 1 := by
          rw [← pow_mul, ← pow_succ']
          exact hy
        rcases ih (y ^ 2) hh with hh | hh
        · exact huniq y hh
        · exact (hroot y (hh.trans hxz.symm)).elim
    have hcard2 : Nat.card P = 2 := by
      apply (Nat.card_eq_two_iff' (1 : P)).mpr
      refine ⟨x, hxne, ?_⟩
      intro y hy
      obtain ⟨n, hn⟩ := hP.exists_pow_pow_eq_one y
      exact ((hall n y hn).resolve_left hy).trans hxz.symm
    omega
  obtain ⟨A, hA, hAc⟩ := hfour
  let := hA
  obtain ⟨V, hV, hVc, hxV⟩ := hP.exists_elementary_four_mem_of_four_le A hAc.ge x hx
  let := hV
  have hnle : ¬ V ≤ zpowers x := by
    intro hh
    have hc := card_le_of_le hh
    rw [hVc, Nat.card_zpowers, hx] at hc
    omega
  obtain ⟨y, hyV, hyout⟩ := SetLike.not_le_iff_exists.mp hnle
  have hyne : y ≠ 1 := fun he => hyout (he ▸ (zpowers x).one_mem)
  refine ⟨y, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian y hyV) hyne,
    fun he => hyout (he ▸ mem_zpowers x), ?_⟩
  exact congrArg Subtype.val (mul_comm' (⟨x, hxV⟩ : V) ⟨y, hyV⟩)
end IsPGroup
