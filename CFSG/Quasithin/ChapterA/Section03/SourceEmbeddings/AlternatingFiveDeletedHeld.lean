module
public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# The Held exclusion for a Sylow-normalized deleted-five block

The characteristic moved layer of the actual block is elementary of order
sixteen. A full Sylow normalizing the block normalizes this literal layer
and contains it. Its Held normalizer has order prime to five, contradicting
the block's alternating-five quotient. The local-component premise is
unnecessary for this particular carrier exclusion.

Source: Aschbacher–Smith A.3.14 and10.2.1, printed pp.49–50,743;
the native Held calculations use GLS3 Table5.3p.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC

/-- The specified Held carrier has no deleted-five block normalized by a full Sylow. -/
theorem alternatingFiveDeleted_not_held {G : Type*} [Group G] [Finite G]
    (e : G ≃* Held.He) (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  let U := (blockU B).map B.subtype
  let := hB.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  have hc : Nat.card U = 16 := (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  have hU : (S : Subgroup G) ≤ normalizer (U : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hUS : U ≤ (S : Subgroup G) := by
    have heq : (S : Subgroup G) ⊔ U = (S : Subgroup G) :=
      S.is_maximal' (S.isPGroup'.to_sup_of_normal_right'
        (IsElementaryAbelian.isPGroup 2 U) hU) le_sup_left
    exact sup_eq_left.mp heq
  have hnot := Held.sylow_normal_sixteen_normalizer_not_five
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (U.map e.toMonoidHom)
    (map_mono hUS) (IsElementaryAbelian.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hc)
    ((map_mono hU).trans (le_normalizer_map e.toMonoidHom))
  rw [← map_equiv_normalizer_eq U e, card_map_of_injective e.injective] at hnot
  obtain ⟨a⟩ := hB.2.2.quotient_iso
  have hq : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hd : 5 ∣ Nat.card B := (show 5 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hq]; decide).trans
    (pCore 2 B).card_quotient_dvd_card
  exact hnot (hd.trans (card_dvd_of_le (B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (blockU B)))))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
