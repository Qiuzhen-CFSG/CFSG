module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Five-rank-zero blocks have odd binary degree

For a chi-zero block with a quasisimple core quotient, the alternating
three row contradicts perfectness and the alternating five row has
five-elements. The remaining binary row has odd degree: even degree makes
five divide q²-1. The semilinear automorphism theorem identifies the outer
group order with that degree.

Source: Aschbacher--Smith C.1.12 and the comparison in 14.6.15, p.1035.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

private theorem not_five_core_of_rank_zero (hr : primeRank 5 L = 0) :
    ¬5 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact fun hd => (PrimeRank.eq_zero_iff_not_dvd_card.mp hr)
    (hd.trans (card_quotient_dvd_card _))

omit [Finite L] in
/-- The binary block has precisely the field-degree outer automorphism order. -/
theorem IsL2EvenBlock.outer_card {n : ℕ} (h : IsL2EvenBlock L n) :
    Nat.card (MulAut.Outer (L ⧸ pCore 2 L)) = n := by
  obtain ⟨_,_,F,_,_,hF,_,hm⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨e⟩ := hm.quotient_iso
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))
  rw [Nat.card_congr (MulAut.outerCongr d).toEquiv]
  exact Theory.PSL2.outer_card_eq_field_degree F hF

/-- An even field degree would make five divide the binary rank-one group order. -/
theorem IsL2EvenBlock.odd_degree_of_five_rank_zero {n : ℕ}
    (h : IsL2EvenBlock L n) (hr : primeRank 5 L = 0) : Odd n := by
  have hc := not_five_core_of_rank_zero hr
  by_contra hn
  have he : Even n := Nat.not_odd_iff_even.mp hn
  obtain ⟨m,hm⟩ := he
  have hd : 5 ∣ (2 ^ n) ^ 2 - 1 := by
    have hh : Nat.ModEq 5 1 (16 ^ m) := by
      simpa only [one_pow] using (show Nat.ModEq 5 1 16 from by decide).pow m
    have heq : (2 ^ n) ^ 2 = 16 ^ m := by
      rw [←pow_mul,hm,show (m+m)*2 = 4*m by omega,pow_mul]
      rfl
    rw [heq]
    exact hh.dvd'
  obtain ⟨_,_,F,_,_,hF,_,hmodel⟩ := h
  obtain ⟨e⟩ := hmodel.quotient_iso
  apply hc
  rw [Nat.card_congr e.toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
  exact dvd_mul_of_dvd_right hd _

/-- A quasisimple chi-zero block without five-elements is binary of odd degree. -/
theorem IsChiZeroBlock.l2Even_of_five_rank_zero
    (h : IsChiZeroBlock L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hr : primeRank 5 L = 0) : ∃ n, IsL2EvenBlock L n ∧ Odd n := by
  rcases h with ⟨n,h⟩ | h | h
  · exact ⟨n,h,h.odd_degree_of_five_rank_zero hr⟩
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    have hc : Nat.card (L ⧸ pCore 2 L) = 3 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num
    let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hc
    let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
    let : Nontrivial (L ⧸ pCore 2 L) := (QuotientGroup.mk'_surjective (center _)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative (L ⧸ pCore 2 L) inferInstance).elim
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    apply (not_five_core_of_rank_zero hr).elim
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num

end CFSG.Quasithin.ChapterC
