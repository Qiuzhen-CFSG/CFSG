module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearDisplacement
public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure

/-!
# Excluding the actual nonbinary doubled linear-three non-FF row

The original orbit has automizer two-rank at most 2n, weak-closure parameter
at most n and now the genuine sharp r bound at least 4n. The completed FWCI
inequality would give r≤3n in the non-FF branch. All parameter producers use
the original same-G,T chosen module; no covering-rank or beta callback remains.
Source: Aschbacher--Smith 7.4.1 and7.5.2, printed pp.700--701.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original nonbinary marked doubled orbit is an FF-module under the
multiple-two-local-overgroup hypothesis. -/
theorem sourceOrbit_linear_FF_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : IsFFModule D.sourceOrbitNormalizerRepresentation := by
  by_contra hnon
  exact Chapter7.natural_dual_parameter_contradiction D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) F.degree_pos
    (D.sourceOrbit_linear_automizer_rank h hd F hmodel)
    (D.sourceOrbit_linear_globalW_le_degree h hd hmany hnon F hn hmodel)
    (D.sourceOrbit_linear_globalR h hd F hn hmodel)

/-- Hence the actual original nonbinary doubled constituent cannot occur in
the marked non-FF source branch. -/
theorem sourceOrbit_linear_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : False :=
  hnon (D.sourceOrbit_linear_FF_of_many h hd hmany F hn hmodel)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
