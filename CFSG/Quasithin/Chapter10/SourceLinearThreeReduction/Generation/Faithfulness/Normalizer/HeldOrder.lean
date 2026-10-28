module
public import Theory.GroupTheory.PerfectPairOrder
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Mathlib.Data.Nat.Squarefree

/-!
# Order obstructions for the remaining Held component

The source C.2.8 covering span has two copies of the centerless seed quotient.
These elementary cardinal and Sylow obstructions are kept separate from the
ambient subgroup transport so they can be reused for the covering and Hall
normalizer branches.

Source: Lagrange, Sylow and Burnside, applied to Aschbacher--Smith
C.3.5 and 4.4.6--12, pp.150,620--623.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
/-- A square divisor of the certified Held order has the indicated bound. -/
theorem held_square_order_bound {n : ℕ} (hn : n ≠ 0)
    (hd : n^2 ∣ 2^12 * (3^3 * 5^2 * 7^3 * 17)) : n ∣ 6720 := by
  have hs : Squarefree (3*7*17 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime (3*7) 17)).mpr
      ⟨(Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).mpr
        ⟨(Nat.prime_iff.mp Nat.prime_three).squarefree,
          (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩,
        (Nat.prime_iff.mp (by decide : Nat.Prime 17)).squarefree⟩
  have hd' : n^2 ∣ 6720^2 * (3*7*17) := hd
  apply (Nat.factorization_le_iff_dvd hn (by decide : 6720 ≠ 0)).mp
  intro p
  have hh := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hn)
    (by decide : 6720^2 * (3*7*17) ≠ 0)).mpr hd' p
  rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
    Nat.factorization_pow] at hh
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh
  have hb := hs.natFactorization_le_one p
  omega

/-- A nontrivial perfect simple group cannot have order dividing 84. -/
theorem no_simple_perfect_order_84 (Q : Type*) [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] (hd : Nat.card Q ∣ 84) : False := by
  have h7 : 7 ∣ Nat.card Q := by
    obtain ⟨p,hp,ho,hp3,hpQ⟩ := Perfect.exists_odd_prime_ne_dvd_card Q Nat.prime_three
    have hp84 : p ∣ 84 := hpQ.trans hd
    have : p = 7 := by
      have hm : p = 2 ∨ p = 3 ∨ p = 7 := by
        have hh : p ∣ 2^2 * 3 * 7 := hp84
        rcases hp.dvd_mul.mp hh with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
        · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
      have hp2 : p ≠ 2 := by
        intro he
        subst p
        exact ho.not_two_dvd_nat (dvd_refl 2)
      omega
    exact this ▸ hpQ
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 Q := Classical.choice inferInstance
  have hcount : Nat.card (Sylow 7 Q) = 1 := by
    have hd' : Nat.card (Sylow 7 Q) ∣ 84 :=
      P.card_dvd_index.trans (P.index_dvd_card.trans hd)
    have hco : Nat.Coprime (Nat.card (Sylow 7 Q)) 7 :=
      ((show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr (not_dvd_card_sylow 7 Q)).symm
    have hd12 : Nat.card (Sylow 7 Q) ∣ 12 := hco.dvd_mul_right.mp hd'
    have hm := Nat.mem_divisors.mpr ⟨hd12,by decide⟩
    have hh : (12 : ℕ).divisors = {1,2,3,4,6,12} := by decide
    rw [hh] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    have hmod := card_sylow_modEq_one 7 Q
    change Nat.card (Sylow 7 Q) % 7 = 1 % 7 at hmod
    omega
  let : Subsingleton (Sylow 7 Q) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let := P.normal_of_subsingleton
  rcases (inferInstance : (P : Subgroup Q).Normal).eq_bot_or_eq_top with hb | ht
  · exact P.ne_bot_of_dvd_card h7 hb
  · have hp : IsPGroup 7 Q := by
      let e : (P : Subgroup Q) ≃* Q := (MulEquiv.subgroupCongr ht).trans topEquiv
      exact P.isPGroup'.of_surjective e.toMonoidHom e.surjective
    exact Group.IsPerfect.not_isNilpotent Q hp.isNilpotent

/-- A doubled odd-rank action on an elementary abelian two-group forces 64 elements. -/
theorem elementary_sixtyFour_dvd_of_doubled_odd_ranks
    (Q E : Type*) [Group Q] [Finite Q] [Nontrivial Q] [Group.IsPerfect Q]
    [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hr : ∀ p : ℕ, p.Prime → Odd p → 2 * primeRank p Q ≤ primeRank p (MulAut E)) :
    2^6 ∣ Nat.card E := by
  have hbig : 32 < Nat.card E := by
    by_contra! hsmall
    have hd : Nat.card (MulAut E) ∣ 2^10 * 3^2 * (5*7*31) := by
      obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
      have hn5 : n ≤ 5 := by
        rw [he] at hsmall
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hsmall
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n he]
      interval_cases n <;> norm_num [Fin.prod_univ_succ]
    have hs : Squarefree (5*7*31 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5*7) 31)).mpr
        ⟨(Nat.squarefree_mul (by decide : Nat.Coprime 5 7)).mpr
          ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
            (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩,
          (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
    exact Perfect.no_doubled_odd_ranks_of_order Q (MulAut E) Nat.prime_three hs hd hr
  obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn6 : 6 ≤ n := by
    rw [he] at hbig
    by_contra! hn6
    have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 5)
    omega
  rw [he]
  exact pow_dvd_pow 2 hn6

/-- Removing a factor eight from this order bound leaves a divisor of 84. -/
theorem dvd_eightyFour_of_dvd_thirteenFortyFour {n : ℕ} (hn : n ≠ 0)
    (hd : n ∣ 1344) (h8 : ¬ 8 ∣ n) : n ∣ 84 := by
  have h2 : n.factorization 2 ≤ 2 := by
    have hh : ¬ 3 ≤ n.factorization 2 := fun h => h8
      ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr h)
    omega
  apply (Nat.factorization_le_iff_dvd hn (by decide : 84 ≠ 0)).mp
  intro p
  have hh := (Nat.factorization_le_iff_dvd hn (by decide : 1344 ≠ 0)).mpr hd p
  change n.factorization p ≤ (2^6 * (3*7) : ℕ).factorization p at hh
  change n.factorization p ≤ (2^2 * (3*7) : ℕ).factorization p
  rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow] at hh ⊢
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh ⊢
  by_cases hp : p = 2
  · subst p
    have hz : (3*7 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide)
    simpa [Nat.prime_two.factorization,hz] using h2
  · have hz : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      exact Finsupp.single_eq_of_ne hp
    simpa only [hz,mul_zero,zero_add] using hh

end CFSG.Quasithin.ChapterC.HypothesisC28
