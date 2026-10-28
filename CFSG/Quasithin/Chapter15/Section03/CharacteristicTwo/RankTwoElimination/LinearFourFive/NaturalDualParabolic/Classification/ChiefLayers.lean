module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.Contract
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.ModuleFactors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.RadicalFactor

/-!
# Coordinate sections for the three parabolic chief factors

This interface exposes the proved ordered flag A < B < C ≤ U ≤ N < E,
relative P-normality of its terms, and the actual quotient isomorphisms and
conjugation formulas for B/A and C/B. They use the original natural-plus-dual
embedding and one common marking of P/O₂(P).

The two module intervals and the radical interval are proved in separate
construction modules and assembled here. Their quotient maps and conjugation
formulas remain the actual maps from the original embedding, so the two dual
sections use the same marking of the point quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The complete marked flag of noncentral chief intervals in the point
parabolic.  The first two sections are the natural and annihilator sections;
the last is the ambient section `O₂(P) / O₂(L)`, with its contragredient
marking supplied by `ambientRadicalQuotientEquiv`. -/
structure ThreeNoncentralChiefIntervals (h : NaturalDual d L) (x : Space 4) : Prop where
  ordered :
    lineSubgroup h x < naturalSubgroup h ∧
      naturalSubgroup h < mixedSubgroup h x ∧
      mixedSubgroup h x ≤ spanCommutator d L ∧
      spanCommutator d L ≤ L.pCoreIn 2 ∧
      L.pCoreIn 2 < (point h x).pCoreIn 2
  natural : IsNoncentralChiefInterval h x (lineSubgroup h x) (naturalSubgroup h)
  mixed : IsNoncentralChiefInterval h x (naturalSubgroup h) (mixedSubgroup h x)
  radical : IsNoncentralChiefInterval h x (L.pCoreIn 2) ((point h x).pCoreIn 2)

/-- The actual three chief factors and their ordered carriers. -/
theorem three_noncentral_chief_intervals [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    ThreeNoncentralChiefIntervals h x := by
  exact {
    ordered := ordered_flag h hx hU
    natural := natural_interval_chief h hx hU
    mixed := mixed_interval_chief h hx hU
    radical := radical_interval_chief h hx }

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
end
