module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# The natural block degree from its actual quotient order

A natural even-field block of degree m has core quotient of order
2^m ((2^m)^2-1). If the actual quotient has order sixty, monotonicity forces
2^m=4 and m=2. This identifies the retained natural type without changing
its model or rebuilding module coordinates.
Source: the classical SL₂ order formula; used in Aschbacher--Smith
10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K]
theorem IsL2EvenBlock.exponent_eq_two_of_quotient_card {m : ℕ}
    (h : IsL2EvenBlock K m) (hq : Nat.card (K ⧸ pCore 2 K)=60) : m=2 := by
  obtain ⟨hm,_,F,_,_,hF,_,ρ,⟨d⟩,_⟩ := h
  have hc : Nat.card SL(2,F)=60 := (Nat.card_congr d.quotientIso.toEquiv).symm.trans hq
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF] at hc
  have hpow : 2^m=4 := by
    have hlo : 4 ≤ 2^m := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2≤m by omega)
      norm_num at hh
      exact hh
    by_contra hn
    have hh : 5 ≤ 2^m := by omega
    have hs : 24 ≤ (2^m)^2-1 := by
      have hh2 := Nat.mul_self_le_mul_self hh
      norm_num at hh2
      rw [←pow_two] at hh2
      omega
    have hp := Nat.mul_le_mul hh hs
    norm_num at hp
    omega
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) (by simpa using hpow)

theorem IsL2EvenBlock.four_of_quotient_card {m : ℕ}
    (h : IsL2EvenBlock K m) (hq : Nat.card (K ⧸ pCore 2 K)=60) : IsL2EvenBlock K 2 :=
  h.exponent_eq_two_of_quotient_card hq ▸ h
end CFSG.Quasithin.ChapterC
