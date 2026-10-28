module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryReciprocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryOddCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJankoPlaced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenBounds
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.OddSubgroups

/-!
# Excluding the original non-FF doubled A7 source row

The reciprocal argument proves uniqueness for the original odd fixed
residual. Every escaping abelian odd normalizer then has an actual J4
component containing the entire orbit, contrary to its original large-center
radical. Characteristic abelian subgroups extend this to every odd actor.
The already proved bounds on that same source orbit give the weak-closure
contradiction. No odd-normalizer, local-classification, or module callback
remains in the final source theorem.
Source: Aschbacher--Smith 4.4.3, 7.3.4, 7.4.1 and 7.5.5,
printed pp.619--623,699--701, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every original abelian odd actor centralizing the full doubled A7 orbit
has its normalizer in the original N(L). -/
theorem sourceOrbit_seven_abelian_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hu := D.sourceOrbit_seven_residual_uniqueness h hd hmany hnon σ hσ hmodel A hA ho
  by_contra hout
  obtain ⟨K,hK,_,_,hcore,_,hr,_,hj⟩ :=
    D.sourceOrbit_seven_oddNormalizer_janko_component h hd σ hmodel A hne hAC ho hu hout
  exact D.sourceOrbit_seven_oddNormalizer_not_janko
    h hd σ hσ hmodel A hAC ho hu K hK hcore hr hj

/-- The literal arbitrary-odd source condition required by the improved
A7 bounds follows from the original chosen-module hypotheses. -/
theorem sourceOrbit_seven_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) : normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  apply odd_normalizer_control_of_abelian ?_ A hne hA ho
  intro B hB hBC hodd hcomm
  let := hcomm
  exact D.sourceOrbit_seven_abelian_oddNormalizer_le
    h hd hmany hnon σ hσ hmodel B hB (hBC.trans inf_le_right) hodd

/-- The original non-FF doubled A7 row is impossible; the full odd-normalizer
premise of the existing weak-closure bounds is discharged internally. -/
theorem sourceOrbit_seven_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    False := by
  exact D.sourceOrbit_seven_false_of_odd_control h hd σ hσ hmodel
    (D.sourceOrbit_seven_oddNormalizer_le h hd hmany hnon σ hσ hmodel) hmany hnon

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
