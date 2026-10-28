module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedLinear
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo

/-!
# Nonbinary exclusions of the actual constrained star models

The original residual action has order at least 20160 and odd prime rank
at least two. Its inner realization is proper, excluding every star model
of order at most 20160, including A₈. This also excludes the triple cover
of A₆ through its genuine central quotient. The nonbinary linear-three,
symplectic and G₂ models are excluded by their literal parabolic action
bounds; the rank-one family is already excluded by C.2.7 geometry.

Consequently the actual C.2.7 star image must be SL₅(2). Cubic rank then
makes its C-component normal in the same H. PushingUpReduction applies
this result with the inclusion-compatible original covering quotient.
The remaining binary-five analysis is retained by the odd-normalizer owner;
this module does not assert the final normalizer theorem.

Source: Aschbacher--Smith C.4.5--8, printed pp.152--154, applied to
4.4.6, printed p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
variable {H M B R W : Subgroup G}

include D S
theorem constrained_natural_core_card_gt
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    20160 < Nat.card (coreCentralQuotient K) :=
  (constrained_natural_action_card D S h hN e K hK hq hout).trans_lt
    (constrained_action_card_lt h K hK hq hout hfK)

theorem no_constrained_natural_small_star
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hc : Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) ≤ 20160) : False := by
  have hb := constrained_natural_core_card_gt D S h hN e K hK hq hout hfK
  have hle : Nat.card (coreCentralQuotient K) ≤
      Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) := by
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  omega

theorem no_constrained_natural_large_linear_three
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (es : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F))
    (hF : 4 ≤ Nat.card F) : False := by
  obtain ⟨p,hp,ho,hr⟩ := constrained_natural_action_rank D S h hN e K hK hq hout
  let : Fact p.Prime := ⟨hp⟩
  have hu := linear_three_span_odd_rank h K hK hq hout hfK es hF ho
  omega

theorem no_constrained_natural_symplectic
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (es : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.symplecticGroup (Fin 2) F) (hF : 4 ≤ Nat.card F) : False := by
  obtain ⟨p,hp,ho,hr⟩ := constrained_natural_action_rank D S h hN e K hK hq hout
  let : Fact p.Prime := ⟨hp⟩
  have hu := h.constrained_symplectic_span_rank_le_one K hK hq hout hfK es hF ho
  omega

theorem no_constrained_natural_g2
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (es : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) : False := by
  obtain ⟨p,hp,ho,hr⟩ := constrained_natural_action_rank D S h hN e K hK hq hout
  let : Fact p.Prime := ⟨hp⟩
  have hu := h.constrained_g2_span_rank_le_one K hK hq hout hfK es hF ho
  omega

omit D S in
private theorem card_linear_three_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card SL(3,F) = 168 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center]
  change Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) = 168
  norm_num [hF,hc]

/-- The literal star-model list reduces to the single binary degree-five row. -/
theorem constrained_natural_star_linear_five_two
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  have hsmall := no_constrained_natural_small_star D S h hN e K hK hq hout hfK
  cases hm with
  | linearTwo F es =>
    exact (h.no_constrained_component_star_linear_two K hK hq hout hfK F es).elim
  | linearThree F es =>
    by_cases hlarge : 1 < F.degree
    · have hF : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      exact (no_constrained_natural_large_linear_three D S h hN e K hK hq hout hfK es hF).elim
    · have hd : F.degree = 1 := by have := F.degree_pos; omega
      apply (hsmall ?_).elim
      rw [Nat.card_congr es.toEquiv,card_linear_three_two (by rw [F.card_eq,hd,pow_one])]
      decide
  | symplectic F hlarge es =>
    apply (no_constrained_natural_symplectic D S h hN e K hK hq hout hfK es ?_).elim
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  | g2 F hlarge es =>
    apply (no_constrained_natural_g2 D S h hN e K hK hq hout hfK es ?_).elim
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  | g2DerivedTwo es =>
    apply (hsmall ?_).elim
    rw [Nat.card_congr es.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
  | alternating n hn es =>
    apply (hsmall ?_).elim
    rw [Nat.card_congr es.toEquiv]
    rcases hn with rfl | rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup] <;> norm_num
  | linearFiveTwo es => exact ⟨es⟩
  | tripleSix ez es =>
    have hb := constrained_natural_core_card_gt D S h hN e K hK hq hout hfK
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv,
      Nat.card_congr es.toEquiv,nat_card_alternatingGroup] at hb
    norm_num at hb

omit D S in
/-- The remaining binary degree-five component is normal in the same H. -/
theorem constrained_linear_five_two_normal
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    K.Normal := by
  apply h.constrained_component_normal_of_star_central_threeRank K hK hq hout hfK
  rw [primeRank_congr 3 (QuotientGroup.congr _ _ e (FixedElementary.map_center e))]
  exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
