module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SmallElementaryLayer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankCoarse
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank

/-!
# The Hall--Janko and Higman--Sims ordinary A₅ rows

The common ordinary source argument makes a nonnormal A₅ pair require an
elementary layer of rank at least eight in the component central quotient.
The Higman--Sims carrier has intrinsic two-rank at most four. For J₂ the
exact carrier order is 604800, whose two-part is only
`2^7`; divisibility of an elementary subgroup order therefore gives the
required bound directly.

Source: Aschbacher--Smith C.4.8, printed pp.153--154, together with the
concrete J₂ and HS carrier calculations in the Atlas-carrier modules.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The ordinary A₅ row with a J₂ component quotient. -/
theorem normalizes_a5_of_ordinary_j2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_twoRank_le_seven a K hK
  rw [primeRank_congr 2 e]
  exact Sporadic.LeechRelated.J2.primeRank_two_le_seven

/-- The ordinary A₅ row with a Higman--Sims component quotient. -/
theorem normalizes_a5_of_ordinary_hs
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_a5_of_ordinary_quotient_twoRank_le_seven a K hK
  rw [primeRank_congr 2 e]
  exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)

end CFSG.Quasithin.ChapterC.HypothesisC28
