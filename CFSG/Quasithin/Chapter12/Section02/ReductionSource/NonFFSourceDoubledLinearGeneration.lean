module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearHall
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryGeneration
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearCartan

/-!
# Original generation bounds for the nonbinary linear-three row

Faithful descent through the full center bounds the actual quotient action
Cartan parameter by the original field degree. The proved Hall kernel
exclusion gives the same bound on every original H-star generation
parameter. E.3.35 then bounds the minimum of the whole-orbit weak-closure
and centralizer parameters. The original global centralizer lower bound
remains necessary before separating this minimum.
Source: Aschbacher--Smith E.3.35--39 and 7.3.4, pp.238--240,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The complete L/O₂(L) conjugation image has Cartan parameter at most n. -/
theorem sourceOrbit_linear_quotientAction_nPrime_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    nPrime (normalizerPCoreQuotientAction L).range ≤ F.degree := by
  let := h.quasisimple
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    (Chapter4.Section02.RankOneReciprocalEscape.centerQuotientCongr m.groupEquiv)
  exact doubledLinear_centralCover_nPrime_le F.card_eq hn e _
    (inner_le_quotientAction_range L)

/-- The original H-star generation parameter is at most the actual field degree. -/
theorem sourceOrbit_linear_generation_le_degree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) : generationParameter H ≤ F.degree := by
  by_cases hsmall : generationParameter H ≤ 1
  · omega
  exact (D.sourceOrbit_linear_generation_le_quotient_nPrime h hd hmany hnon F hn hmodel
    hH (by omega)).trans (D.sourceOrbit_linear_quotientAction_nPrime_le h F hn hmodel)

/-- The original multiple-overgroup hypothesis bounds the actual whole-orbit minimum. -/
theorem sourceOrbit_linear_min_parameters_le_degree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤ F.degree := by
  obtain ⟨H,hH⟩ := D.doubledOrbit_outside_of_many h hmany
  exact (D.sourceOrbit_doubled_min_parameters_le_generation h hd hH).trans
    (by exact_mod_cast D.sourceOrbit_linear_generation_le_degree h hd hmany hnon F hn hmodel hH)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
