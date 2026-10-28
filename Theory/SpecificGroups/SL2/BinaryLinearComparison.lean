module
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import GorensteinWalter.PSL2Cardinality
/-!
# Separating binary rank-one and rank-two linear groups

Binary SL2 has three-rank exactly one. It cannot be isomorphic to binary
SL3: over a field larger than two, a split diagonal torus gives rank two
at an odd prime; the remaining SL3(2) has order 168, outside the SL2 order
formula q(q²−1) for every finite field.

This supplies the model comparison in the full B.5 moved-section dispatcher
used by Aschbacher–Smith C.4.6, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace Matrix.SL2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem binary_threeRank_eq_one : primeRank 3 SL(2,F) = 1 := by
  apply Nat.le_antisymm (binary_odd_primeRank_le_one (by decide : Odd 3))
  apply Nat.one_le_iff_ne_zero.mpr
  intro hz
  have hd := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    ((hd.trans (card_subgroup_dvd_card _)).trans
      (card_dvd_of_surjective (QuotientGroup.mk' (center SL(2,F)))
        (QuotientGroup.mk'_surjective _)))

theorem binary_not_equiv_linear_three
    {E : Type*} [Field E] [Finite E] {n : ℕ} (hn : 0 < n)
    (hcE : Nat.card E = 2^n) (e : SL(2,F) ≃* SL(3,E)) : False := by
  by_cases he : 1 < n
  · have hq : 1 < Nat.card E - 1 := by
      rw [hcE]
      have := Nat.pow_lt_pow_right (a := 2) (by decide) he
      norm_num at this
      omega
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card E - 1 ≠ 1)
    have ho : Odd p := Odd.of_dvd_nat (by
      rw [hcE]
      have hpos : 0 < 2 ^ n := pow_pos (by decide) _
      have hmod := Nat.even_iff.mp (even_two.pow_of_ne_zero (Nat.ne_of_gt hn))
      exact Nat.odd_iff.mpr (by omega)) hd
    let : Fact p.Prime := ⟨hp⟩
    have hr := Theory.SpecificGroups.Classical.PairedOddRank.linear_special_of_dvd hp hd
    have hs := binary_odd_primeRank_le_one (F := F) ho
    rw [primeRank_equiv p e] at hs
    omega
  have hE : n = 1 := by omega
  have hcardE : Nat.card E = 2 := by rw [hcE,hE]; norm_num
  have hcenter : center SL(3,E) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hcardE]
    norm_num
  have hc : Nat.card SL(3,E) = 168 := by
    let eqp : SL(3,E) ≃* PSL(3,E) :=
      (QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq hcenter.symm)
    rw [Nat.card_congr eqp.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcardE]
    norm_num
  have hh := Nat.card_congr e.toEquiv
  rw [GorensteinWalter.sl2_card_formula,hc] at hh
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hb : Nat.card F ≤ 5 := by
    by_contra h
    have hlarge : 6 ≤ Nat.card F := by omega
    have hsq : 36 ≤ Nat.card F ^ 2 := by nlinarith
    have hsub : 35 ≤ Nat.card F ^ 2 - 1 := by omega
    nlinarith
  generalize Nat.card F = q at hh hq hb
  interval_cases q <;> norm_num at hh
end Matrix.SL2
