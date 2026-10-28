module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ProjectionOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ResidualCases
public import Theory.SpecificGroups.Held.TwoRank.Extension
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Three remaining ordinary sporadic rows have insufficient two-part

The actual natural module and its full actor quotient force 2¹² to divide
an ordinary component's central quotient. The certified M₂₄ and J₂ orders
contradict this. For Held, the checked 1024-word Sylow cover suffices;
no ambient order or simplicity calculation is needed.

FinalOrdinary applies these exclusions to the original covering residual.
Source: Aschbacher--Smith C.3.5, p.150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem held_not_two_pow_twelve : ¬ 2 ^ 12 ∣ Nat.card Held.He := by
  obtain ⟨P,hP⟩ := Held.LocalPairs.SylowGeometry.Calculations.exists_representative_sylow
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq
  intro hd
  have hdP := P.pow_dvd_card_of_pow_dvd_card hd
  have hc : Nat.card P ≤ 1024 := by
    rw [hP]
    exact (Nat.card_le_card_of_surjective _
      Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.normalForm_surjective).trans
      (by simp)
  have hp := Nat.le_of_dvd (Nat.card_pos (α := P)) hdP
  norm_num at hp
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original ordinary component is neither M₂₄, J₂ nor He. -/
theorem no_ordinary_natural_small_sylow {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (K : Subgroup H) (hK : IsComponent H K)
    (n : ClassificationModels.SporadicName) (hn : n = .m24 ∨ n = .j2 ∨ n = .he)
    (ek : K ⧸ center K ≃* n.Carrier) : False := by
  have hd := ordinary_natural_two_power_dvd D S h hBL hc hVB K hK
  rw [Nat.card_congr ek.toEquiv] at hd
  rcases hn with rfl | rfl | rfl
  · change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M24 at hd
    rw [Sporadic.Mathieu.m24_order] at hd
    norm_num at hd
  · change 2 ^ 12 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
    norm_num at hd
  · exact held_not_two_pow_twelve hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
