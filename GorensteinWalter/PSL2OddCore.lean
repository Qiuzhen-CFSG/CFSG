module
public import GorensteinWalter.PSL2CoreModelFacts
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.PPrimeCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import GorensteinWalter.AlternatingFourThreeSubgroupNormalizer

/-!
# Trivial odd core in every odd PSL2 model

For a finite field of odd prime-power order, PSL2 has trivial odd core,
including field order three. Above three, simplicity and the actual even
Sylow order exclude a nontrivial normal odd subgroup. At three, the actual
A4 model has order twelve: an odd normal subgroup has order one or three,
and the proved self-normalizing property excludes the latter.

This model fact supplies the odd-core reduction for prescribed index-two
PGL2 extensions in Alperin--Brauer--Gorenstein, Chapter II, Section 3,
Proposition 3 (article page 25, PDF page 26). No perfectness is assumed at field order
three, and no ambient classification hypothesis is needed.
-/

namespace GorensteinWalter
universe u

public theorem psl2_pPrimeCore_two_eq_bot
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    pPrimeCore 2 (PSL2 K) = ⊥ := by
  classical
  by_cases hthree : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hthree)
    let e := (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
    let O := pPrimeCore 2 (PSL2 K)
    have hcard : Nat.card (PSL2 K) = 12 := by
      rw [psl2_card_formula K hK, hthree]
      norm_num
    have hd : Nat.card O ∣ 12 := hcard ▸ O.card_subgroup_dvd_card
    have ho : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hpos : 0 < Nat.card O := Nat.card_pos
    have hle : Nat.card O ≤ 12 := Nat.le_of_dvd (by decide) hd
    have hn2 := ho.not_two_dvd_nat
    have hc : Nat.card O = 1 ∨ Nat.card O = 3 := by
      interval_cases h : Nat.card O <;> simp_all
    rcases hc with hc | hc
    · exact Subgroup.card_eq_one.mp hc
    · have hnorm := normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
        O hc ⟨e⟩
      have htop : O = ⊤ := by
        rw [Subgroup.normalizer_eq_top] at hnorm
        exact hnorm.symm
      rw [htop, Subgroup.card_top, hcard] at hc
      omega
  · have hlarge : 3 < Nat.card K := lt_of_le_of_ne
      (odd_prime_power_three_le _ hK) (Ne.symm hthree)
    let : IsSimpleGroup (PSL2 K) := by
      exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    rw [pPrimeCore_eq_bot_iff]
    intro O hOn hOc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O hOn with hbot | htop
    · exact hbot
    · exfalso
      have hdih := psl2_odd_hasDihedralSylowTwo_model K hK
      let S : Sylow 2 (PSL2 K) := Classical.choice Sylow.nonempty
      obtain ⟨m, _hm, ⟨eS⟩⟩ := hdih S
      have hScard : Nat.card (S : Subgroup (PSL2 K)) = 2 * 2 ^ m :=
        (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
      have heven : 2 ∣ Nat.card (PSL2 K) :=
        (show 2 ∣ Nat.card (S : Subgroup (PSL2 K)) by rw [hScard]; simp).trans
          S.card_subgroup_dvd_card
      rw [htop, Subgroup.card_top] at hOc
      have := hOc.eq_one_of_dvd heven
      omega

end GorensteinWalter
