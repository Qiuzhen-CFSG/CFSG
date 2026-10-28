module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Rudvalis.Model.Basic

/-!
# Odd-rank reduction for the Rudvalis converse

The source order has odd prime cubes only at three and five. A nonabelian
subgroup of order 27 or 125 embeds in a Sylow subgroup of that same order,
so its Sylow subgroup is nonabelian and has prime rank at most two. The
cube-free criterion handles every other odd prime.

This is a conditional reduction: the ambient order and the two actual
nonabelian subgroups must still be supplied. It does not infer Sylow
noncommutativity from the order factorization alone.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), p.482; GLS3 Table 5.3r, p.279. The carrier is exactly
the existing degree-4060 ATLAS permutation model.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuRank
open Subgroup Rudvalis

private theorem odd_cube_not_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hne3 : p ≠ 3) (hne5 : p ≠ 5) : ¬ p ^ 3 ∣ 145926144000 := by
  intro hd
  have hpd : p ∣ 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  simp only [hp.dvd_mul] at hpd
  have prime_eq {q : ℕ} (hq : q.Prime) (h : p ∣ q) : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp h
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 29 := by
    rcases hpd with ((((h2 | h3) | h5) | h7) | h13) | h29
    · exact Or.inl (prime_eq (by decide) (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl (prime_eq (by decide) (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl (prime_eq (by decide) (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_eq (by decide) h7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prime_eq (by decide) h13)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prime_eq (by decide) h29)))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact hne3 rfl
  · exact hne5 rfl
  · norm_num at hd
  · norm_num at hd
  · norm_num at hd

private theorem sylow_cube_of_subgroup {p : ℕ} [Fact p.Prime]
    (P : Subgroup Model) (hc : Nat.card P = p ^ 3) (hna : ¬ IsMulCommutative P)
    (hambient : Nat.card Model = 145926144000) (hp : p = 3 ∨ p = 5) :
    ∃ S : Sylow p Model, Nat.card S = p ^ 3 ∧ ¬ IsMulCommutative S := by
  obtain ⟨S, hPS⟩ := (IsPGroup.of_card hc).exists_le_sylow
  refine ⟨S, ?_, ?_⟩
  · rw [S.card_eq_multiplicity, hambient]
    rcases hp with rfl | rfl <;> decide +kernel
  · intro hS
    apply hna
    exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
      (isMulCommutative_iff_of_setLike.mp hS) x (hPS hx) y (hPS hy)

/-- Concrete nonabelian prime-cube subgroups discharge all odd-rank cases. -/
public theorem stronglyQuasithin_of_subgroups
    (hcard : Nat.card Model = 145926144000)
    (h3 : ∃ P : Subgroup Model, Nat.card P = 3 ^ 3 ∧ ¬ IsMulCommutative P)
    (h5 : ∃ P : Subgroup Model, Nat.card P = 5 ^ 3 ∧ ¬ IsMulCommutative P) :
    IsStronglyQuasithin Model := by
  apply stronglyQuasithin_of_odd_sylow_cases
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_cases hthree : p = 3
  · subst p
    obtain ⟨P, hc, hna⟩ := h3
    exact Or.inr (sylow_cube_of_subgroup P hc hna hcard (Or.inl rfl))
  by_cases hfive : p = 5
  · subst p
    obtain ⟨P, hc, hna⟩ := h5
    exact Or.inr (sylow_cube_of_subgroup P hc hna hcard (Or.inr rfl))
  · apply Or.inl
    rw [hcard]
    exact odd_cube_not_dvd hp ho hthree hfive

end CFSG.Quasithin.MainConverse.SporadicLocal.RuRank
