module

public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve

/-!
# The triple-cover row in the Cartan component sieve

The full cover local-rank theorem leaves an odd-degree binary unitary cover
when the ordinary three-rank is at most one. Its ordinary three-rank is two,
so that exception is impossible as well. This uses the actual center and
all four A.3.6 cover constructors, including the field-four linear cover.

The original Geometry application is in `Sieve.Noncentral`. The remaining
nilpotent-Fitting row stays with qt-d-1222-natural-closure-cartan.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781;
the imported cover theorem is A.2.12(I.i), p.36.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- A triple cover from the full A.3.6 list has three-rank at least two.
The argument retains the binary unitary exception until its ordinary
three-rank calculation excludes it. -/
theorem three_cover_not_small_rank {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hm : ThreeCoverModel Q) (hz : Nonempty (center Q ≃* Multiplicative (ZMod 3)))
    (hr : primeRank 3 Q ≤ 1) : False := by
  have hc : Nat.card (center Q) = 3 := by
    rw [Nat.card_congr hz.some.toEquiv]
    exact Nat.card_zmod 3
  obtain ⟨n,hn,ho,hmodel⟩ := OddCenterCovers.unitary_model_of_threeCover_local_rank_le_one
    hm hc ((twoLocalPrimeRank_le_primeRank 3).trans hr)
  have hh := OddCenterCovers.unitary_special_threeRank_eq_two (by omega : 0 < n) ho hmodel
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
