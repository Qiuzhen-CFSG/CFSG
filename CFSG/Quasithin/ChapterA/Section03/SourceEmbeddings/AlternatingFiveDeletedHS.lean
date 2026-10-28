module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# The HS exclusion for a Sylow-normalized deleted-five block

The actual deleted module is elementary of order sixteen and characteristic
in the block. A full Sylow normalizing the block therefore normalizes this
same elementary subgroup, contradicting the intrinsic HS bound of eight.
No local-component or normalizer-control assumption is required.

Source: Aschbacher–Smith A.3.14 and 10.2.1, printed pp.49,743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC Sporadic.LeechRelated.HS

/-- The specified HS carrier has no deleted-five block normalized by its full Sylow. -/

theorem alternatingFiveDeleted_not_hs {G : Type*} [Group G] [Finite G]
    (e : G ≃* Carrier) (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  let U := (blockU B).map B.subtype
  let := hB.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  have hc : Nat.card U = 16 := (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  have hU : (S : Subgroup G) ≤ normalizer (U : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hh := normal_elementary_card_le_eight (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (U.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
    ((map_mono hU).trans (le_normalizer_map e.toMonoidHom))
  rw [card_map_of_injective e.injective,hc] at hh
  omega
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
