module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Odd ranks of the binary linear models

The orders of PSL₃(2), PSL₄(2), and PSL₅(2) divide
`2^10 * 3^2 * 5 * 7 * 31`. No odd prime cube divides this number, so the
ordinary odd-prime ranks, and hence the ranks in every actual 2-local, are
at most two. The order calculation applies to any field of cardinality two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1–2), printed p.4, repeated on p.482. This module proves
the QT clause; even characteristic is a separate local calculation.
-/

namespace CFSG.Quasithin.MainConverse

open scoped MatrixGroups

private theorem binary_linear_card_dvd {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) :
    Nat.card PSL(n, F) ∣ 9999360 := by
  have : NeZero n := ⟨by rcases hn with rfl | rfl | rfl <;> decide⟩
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rcases hn with rfl | rfl | rfl
  all_goals
    norm_num [hF, Fin.prod_univ_succ] at h
    norm_num [h]

private theorem binary_linear_odd_cube_not_dvd {p : ℕ}
    (hp : p.Prime) (ho : Odd p) : ¬ p ^ 3 ∣ 9999360 := by
  intro hd
  have hpd : p ∣ 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hcases : 2 = p ∨ 3 = p ∨ 5 = p ∨ 7 = p ∨ 31 = p := by
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp
              (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl
            (((by norm_num : Nat.Prime 5).dvd_iff_eq hp.ne_one).mp h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (((by norm_num : Nat.Prime 7).dvd_iff_eq hp.ne_one).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (((by norm_num : Nat.Prime 31).dvd_iff_eq hp.ne_one).mp h))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  all_goals norm_num at hd

/-- Ordinary odd-prime ranks of the three binary linear carriers are at most two. -/
public theorem binary_linear_stronglyQuasithin {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) :
    IsStronglyQuasithin PSL(n, F) := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  intro hd
  exact binary_linear_odd_cube_not_dvd hp ho (hd.trans (binary_linear_card_dvd hF hn))

/-- The binary cases with the arbitrary finite-field witness used by `IsPSL`. -/
public theorem binary_linear_quasithin {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hG : ClassicalGroup.IsPSL G n 2) : IsQuasithin G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  exact Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (binary_linear_stronglyQuasithin hcard hn).quasithin

end CFSG.Quasithin.MainConverse
