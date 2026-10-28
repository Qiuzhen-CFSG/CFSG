module
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryOffender.FourDimensionalCubic
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Rank-one starred actors from a rank deficit

If the quadratic ratio is two, a nontrivial elementary actor cannot have
fixed codimension at most its rank, by Thompson replacement. A rank deficit
of at most one is therefore exact. If the actor rank is at most two and the
cubic ratio is two as well, rank two would give a cubic four-group of ratio
three halves. Thus the actor has order two, fixed codimension two, and is
an inclusion-minimal cubic minimum actor.

Source: Aschbacher--Smith 15.1.13(3), printed p.1091, using B.2.4(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem codimension_eq_rank_add_one_of_deficit
    (ρ : Representation (ZMod 2) D W) (hq : quadraticRatio ρ = 2)
    {A : Subgroup D} (hA : IsElementaryTwo A)
    (hdef : fixedCodim ρ A ≤ rank A + 1) : fixedCodim ρ A = rank A + 1 := by
  have hnot : ¬ fixedCodim ρ A ≤ rank A := by
    intro hc
    have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp ⟨A,hA,hc⟩
    rw [hq] at hh
    norm_num at hh
  omega

theorem rank_one_starred_of_rank_deficit
    (ρ : Representation (ZMod 2) D W) (hq : quadraticRatio ρ = 2)
    (hhat : cubicRatio ρ = 2) {A : Subgroup D} (hA : IsElementaryTwo A)
    (hrank : rank A ≤ 2) (hdef : fixedCodim ρ A ≤ rank A + 1) :
    Nat.card A = 2 ∧ rank A = 1 ∧ fixedCodim ρ A = 2 ∧ A ∈ QhatStar ρ := by
  have hcod := codimension_eq_rank_add_one_of_deficit ρ hq hA hdef
  have hr : rank A = 1 := by
    have hp := hA.rank_pos
    by_contra hn
    have hr2 : rank A = 2 := by omega
    have hc4 : Nat.card A = 4 := by rw [hA.card_eq_two_pow_rank,hr2]; norm_num
    have hcub := isCubic_of_elementary_card_four ρ A hA.2 hc4
    have hl : (2 : ℝ≥0∞) ≤ actionRatio ρ A := by
      rw [←hhat]
      exact iInf_le_of_le A (iInf_le_of_le ⟨hA,hcub⟩ le_rfl)
    rw [actionRatio,hcod,hr2] at hl
    norm_num [ENNReal.le_div_iff_mul_le] at hl
  have hc2 : Nat.card A = 2 := by rw [hA.card_eq_two_pow_rank,hr]; norm_num
  have hd : fixedCodim ρ A = 2 := by omega
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hA.1
  have ht : orderOf (a : D) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (a : D) a.property)
    (fun h => ha (Subtype.ext h))
  have he : zpowers (a : D) = A := eq_of_le_of_card_ge (zpowers_le.mpr a.property) (by
    rw [hc2,Nat.card_zpowers,ht])
  have hquad : IsQuadratic ρ A := by
    rw [←he]
    exact (involution_actor_rank_and_fixedCodim ρ a ht).2.2.1
  refine ⟨hc2,hr,hd,⟨⟨hhat.le,hA,isCubic_of_isQuadratic hquad,?_⟩,?_⟩⟩
  · rw [actionRatio,hr,hd,hhat]
    norm_num
  · intro B hB hBA
    exact eq_of_le_of_card_ge hBA (by
      rw [hc2]
      have hh := (one_lt_card_iff_ne_bot B).mpr hB.2.1.1
      omega)
end CFSG.Quasithin.ChapterD
