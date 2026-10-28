module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.OddQuotients

/-!
# The fixed alternatives in the classical parameter comparison

The orders of PSL₄(2), PSL₅(2), and A₇ divide
`2^10 * 3^2 * 5 * 7 * 31`. No odd prime cube divides that number,
whereas the defining-prime root group of PSL₃(p) or PSU₃(p) has order p³.
These divisibility facts separate the actual carriers.

The binary order argument is adapted from the private calculations in
`MainConverse/EvenLinearLocal/BinaryRank.lean`, using the same attributed
ATLAS order formula; see `LICENSES/ATLAS.txt`.
Source: Aschbacher–Smith, F.9.18(4), printed pp.325–326, and 13.8.17, p.953.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
private theorem binary_card_dvd {G : Type*} [Group G] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : ClassicalGroup.IsPSL G n 2) :
    Nat.card G ∣ 9999360 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rcases hn with rfl | rfl
  all_goals
    norm_num [hF, Fin.prod_univ_succ] at hc
    norm_num [hc]

private theorem odd_cube_not_dvd {p : ℕ}
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

private theorem alternating_seven_card_dvd : Nat.card (alternatingGroup (Fin 7)) ∣ 9999360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num

open Chapter1.Section02.LocalModels

/-- Odd-prime degree-three projective models cannot be the fixed binary linear alternatives. -/
theorem odd_projective_not_binary {S : Type*} [Group S] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) {unitary : Bool} (h : IsPSLSign S unitary 3 p)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ ClassicalGroup.IsPSL S n 2 := by
  intro hb
  exact odd_cube_not_dvd hp ho ((prime_cube_dvd_card hp h).trans (binary_card_dvd hn hb))

/-- The same root-order obstruction excludes A₇, without a recognition assumption. -/
theorem odd_projective_not_alternating_seven {S : Type*} [Group S] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) {unitary : Bool} (h : IsPSLSign S unitary 3 p) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  have hd := prime_cube_dvd_card hp h
  rw [Nat.card_congr e.toEquiv] at hd
  exact odd_cube_not_dvd hp ho (hd.trans alternating_seven_card_dvd)

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
