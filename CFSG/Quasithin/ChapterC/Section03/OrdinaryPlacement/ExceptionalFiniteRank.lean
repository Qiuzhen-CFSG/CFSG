module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SmallElementaryLayer
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# The Held and Rudvalis rows of the original A₅ local source

The original nonnormal A₅ pair would act with five-rank at least two on
an elementary layer of the ordinary component's central quotient. The
shared source action theorem forces that layer to have rank at least eight.
Both actual finite models have two-rank at most six, yielding local normality.

Source: Aschbacher--Smith C.3.5 and C.4.8, printed pp.150--153, in the
A₅ covering configuration of 4.2.12--13, pp.610--611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The actual Held central quotient forces normalization of the original A₅ component. -/
theorem normalizes_a5_of_ordinary_held
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Held.He) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_twoRank_le_seven a K hK
  rw [primeRank_congr 2 e]
  exact Held.primeRank_two_le_six.trans (by decide)

/-- The actual Rudvalis central quotient forces normalization of the original A₅ component. -/
theorem normalizes_a5_of_ordinary_rudvalis
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Rudvalis.Model) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_twoRank_le_seven a K hK
  rw [primeRank_congr 2 e]
  exact Rudvalis.primeRank_le_six.trans (by decide)

end CFSG.Quasithin.ChapterC.HypothesisC28
