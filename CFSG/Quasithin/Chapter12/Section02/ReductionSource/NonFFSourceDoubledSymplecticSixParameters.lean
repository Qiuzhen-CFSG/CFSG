module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticSix
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBounds
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!+# Initial global bounds for the genuine A₆ doubled orbit

The deleted six-letter seed is marked as Sp₄(2)′. Its actual conjugator
gives the graph pair and the full ambient automizer estimates m ≥ 3 and
a < 2. The literal E.6.1 setup and the proved E.6.3 theorem then give
r ≥ m. Thus the original weak-closure inequality forces w > 1.

These statements apply to the original chosen orbit and every ambient
centralizer, rather than only to its model coordinates. The opposite
bound w ≤ 1 in source 7.3.4 remains necessary for the final exclusion.
Source: Aschbacher--Smith E.6.3, H.7 and 7.3.2--7.3.5,
printed pp.245,388--389,698--699 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The binary derived row satisfies r ≥ m, m ≥ 3 and the strict a < 2
on the same original orbit and its full ambient automizer. -/
theorem sourceOrbit_six_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    (localM D.sourceOrbit : ℕ∞) ≤ globalR D.sourceOrbit ∧
      3 ≤ localM D.sourceOrbit ∧ localA D.sourceOrbit < (2 : ℕ∞) := by
  obtain ⟨hm,ha⟩ := D.sourceOrbit_six_local_parameters h hd hmodel
  have hE := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  exact ⟨(Section06.FrobeniusReduction.lower_bound_knownSimple hE (by omega)).1,hm,ha⟩

/-- All subspaces below the original local corank threshold have their full
ambient centralizer in the original component normalizer. -/
theorem sourceOrbit_six_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {U : Subgroup G} (hU : U ≤ D.sourceOrbit)
    (hc : subgroupCorank D.sourceOrbit U < localM D.sourceOrbit) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hr := (D.sourceOrbit_six_initial_parameters h hd hmodel).1
  have hC := centralizer_le_normalizer_of_corank_lt_globalR hU
    ((ENat.natCast_lt_natCast.mpr hc).trans_le hr)
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hC

/-- The actual weak-closure contradiction forces w > 1 in the A₆ row.
Source 7.3.4 must still provide w ≤ 1 to exclude this row. -/
theorem sourceOrbit_six_globalW_gt_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    (1 : ℕ∞) < globalW D.sourceOrbit T := by
  apply lt_of_not_ge
  intro hw
  obtain ⟨hr,hm,ha⟩ := D.sourceOrbit_six_initial_parameters h hd hmodel
  exact DoubledSymplecticBounds.false D.sourceOrbit T (n := 1)
    ⟨hr,hm,ha,hw⟩ D.sourceOrbit_weakClosure_setup

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
