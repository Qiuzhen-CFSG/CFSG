module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedLocals
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedFinite
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Exhausting the constrained C.2.8 component branch

The genuine C.2.7 star catalogue, including central covers, is exhausted
using the literal action and radical intersection. The large binary rows
use their local structure, and the remaining rows use the section-order
obstruction. No component classification or action callback remains.

Source: Aschbacher--Smith C.2.7 and 4.2.12--13, pp.146--147,610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface


/-- The original normalized actor excludes every actual constrained C.2.7 model. -/
theorem no_constrained_normalized_rankOne
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (hsize : 20160 < Nat.card S) (hl5 : ¬ Nat.card S ∣ 9999360)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo E e => exact h.no_constrained_component_star_linear_two K hK hq hout hfK E e
  | linearThree E e =>
    by_cases hE : 1 < E.degree
    · exact no_constrained_normalized_linear_three h hn hS hexp π hπ K hK hq hout hfK E hE e
    · have hdeg : E.degree = 1 := by have := E.degree_pos; omega
      apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
      rw [Nat.card_congr e.toEquiv]
      have hc := (center SL(3,E.Carrier)).index_mul_card
      rw [Atlas.ExceptionalSupport.card_sl_center] at hc
      change Nat.card PSL(3,E.Carrier) * Nat.gcd 3 (Nat.card E.Carrier - 1) = _ at hc
      rw [←hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar,E.card_eq,hdeg]
      norm_num
  | symplectic E hE e =>
    apply no_constrained_normalized_symplectic h hn hS hexp π hπ K hK hq hout hfK e
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2 E hE e =>
    apply no_constrained_normalized_g2 h hn hS hexp π hπ K hK hq hout hfK e
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2DerivedTwo e =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    norm_num
  | alternating n hdegree e =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    rw [Nat.card_congr e.toEquiv]
    rcases hdegree with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num
  | linearFiveTwo e =>
    exact no_constrained_normalized_linear_five_two h hn hS π hπ hl5 K hK hq hout hfK e
  | tripleSix ez eq =>
    apply no_constrained_normalized_small_star h hn hS π hπ hsize K hK hq hout hfK
    let C := starImage (K.map H.subtype) R (K.map H.subtype)
    have hc := (center C).index_mul_card
    change Nat.card (C ⧸ center C) * Nat.card (center C) = Nat.card C at hc
    rw [Nat.card_congr eq.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc
    rw [←hc]
    norm_num

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

end
