module
public import ABG.ChapterII.Section1.PresentationCalculus
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Summation over a semidihedral group of order sixteen

A function constant on elements of each nontrivial order has sum
`f 1 + 5 v₂ + 6 v₄ + 4 v₈`. The sixteen bounded normal forms give a
bijection with `Fin 8 × Fin 2`; the presentation computes their orders.
No ambient fusion or character-theoretic hypothesis is needed.

Source: ABG II.1 Lemma 1 and the Sylow sum in III.6 Corollary 6.
-/

open scoped BigOperators
namespace ABG.QuasiDihedral
noncomputable section
attribute [local instance] Fintype.ofFinite

/-- The order census, expressed as a sum for functions constant on each order. -/
public theorem sum_order_sixteen {H : Type*} [Group H] [Finite H]
    (hH : Stellmacher.IsSemidihedralGroup H) (hc : Nat.card H = 16)
    (f : H → ℂ) (v₂ v₄ v₈ : ℂ)
    (h₂ : ∀ y, orderOf y = 2 → f y = v₂)
    (h₄ : ∀ y, orderOf y = 4 → f y = v₄)
    (h₈ : ∀ y, orderOf y = 8 → f y = v₈) :
    ∑ y : H, f y = f 1 + 5 * v₂ + 6 * v₄ + 4 * v₈ := by
  classical
  obtain ⟨n, a, b, hn, hcard, ha, hb, hab, _, hnf⟩ := exists_normal_form hH
  have hn4 : n = 4 := by
    have he : 2 ^ n = 2 ^ 4 := hcard.symm.trans hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) he
  subst n
  norm_num at ha hab hnf
  let nf : Fin 8 × Fin 2 → H := fun p => if p.2 = 0 then a ^ p.1.val else a ^ p.1.val * b
  have hsur : Function.Surjective nf := by
    intro y
    obtain ⟨i, hi, hy | hy⟩ := hnf y
    · exact ⟨(⟨i, hi⟩, 0), by simpa [nf] using hy.symm⟩
    · exact ⟨(⟨i, hi⟩, 1), by simpa [nf] using hy.symm⟩
  have hbij : Function.Bijective nf := (Fintype.bijective_iff_surjective_and_card nf).mpr
    ⟨hsur, by simp [← Nat.card_eq_fintype_card, hc, Nat.card_fin]⟩
  have hne (i : Fin 8) : a ^ i.val * b ≠ 1 := by
    intro hi
    have he : nf (i, 1) = nf (0, 0) := by simpa [nf] using hi
    have := congrArg Prod.snd (hbij.1 he)
    exact (by decide : (1 : Fin 2) ≠ 0) this
  have hsq (i : Fin 8) : (a ^ i.val * b)^2 = a ^ ((4*i.val)%8) := by
    rw [outer_square (n := 4) (by decide) a b hb hab]
    norm_num only
    exact (pow_mod_orderOf a (4*i.val)).symm.trans (by rw [ha])
  have ha4 : a^4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [ha] at this
    norm_num at this
  have hout (i : Fin 8) : orderOf (a ^ i.val * b) = ![2,4,2,4,2,4,2,4] i := by
    have hs := hsq i
    have hi := hne i
    fin_cases i <;> norm_num at hs hi ⊢
    all_goals first
      | exact orderOf_eq_prime hs hi
      | apply orderOf_eq_prime_pow (p := 2) (n := 1)
        · simpa only [show 2^1 = 2 from rfl, hs] using ha4
        · rw [show 2^(1+1) = 2*2 from rfl, pow_mul, hs, ← pow_mul]
          simpa only [ha] using pow_orderOf_eq_one a
  have hin (i : Fin 8) : orderOf (a ^ i.val) = ![1,8,4,8,2,8,4,8] i := by
    rw [orderOf_pow, ha]
    fin_cases i <;> norm_num
  have hv (i : Fin 8) : f (a ^ i.val) = ![f 1,v₈,v₄,v₈,v₂,v₈,v₄,v₈] i := by
    have hi := hin i
    fin_cases i <;> norm_num at hi ⊢
    all_goals first | exact h₂ _ hi | exact h₄ _ hi | exact h₈ _ hi
  have hw (i : Fin 8) : f (a ^ i.val * b) = ![v₂,v₄,v₂,v₄,v₂,v₄,v₂,v₄] i := by
    have hi := hout i
    fin_cases i <;> norm_num at hi ⊢
    all_goals first | exact h₂ _ hi | exact h₄ _ hi
  rw [← hbij.sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, nf, Fin.isValue, ite_true,
    show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  simp_rw [hv, hw]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring
end
end ABG.QuasiDihedral
