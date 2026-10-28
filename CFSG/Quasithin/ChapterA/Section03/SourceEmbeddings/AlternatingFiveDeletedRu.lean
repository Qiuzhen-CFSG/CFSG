module
public import Theory.SpecificGroups.Rudvalis.Model.SylowElementarySixteen
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# The Rudvalis exclusion for a Sylow-normalized deleted-five block

The characteristic deleted module has order sixteen. Its normalizer contains
both the given block and the full Sylow. The A₅ quotient forces five to divide
this normalizer's order, contradicting the native Rudvalis catalogue.

Source: Aschbacher–Smith A.3.14 and 10.2.1, printed pp.49,743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC

/-- No deleted-five block in Rudvalis is normalized by a full Sylow. -/
theorem alternatingFiveDeleted_not_ru_native
    (S : Sylow 2 Rudvalis.Model) (B : Subgroup Rudvalis.Model)
    (hB : IsAlternatingBlock B 5)
    (hn : (S : Subgroup Rudvalis.Model) ≤ normalizer (B : Set Rudvalis.Model)) : False := by
  let U := (blockU B).map B.subtype
  let := hB.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  have hc : Nat.card U = 16 := (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  have hSN : (S : Subgroup Rudvalis.Model) ≤ normalizer (U : Set Rudvalis.Model) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hBN : B ≤ normalizer (U : Set Rudvalis.Model) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (blockU B))
  apply Rudvalis.SylowElementarySixteen.normalizer_sixteen_not_five S U inferInstance hc hSN
  obtain ⟨a⟩ := hB.2.2.quotient_iso
  have hcard : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
    norm_num
  apply dvd_trans (b := Nat.card B) _ (card_dvd_of_le hBN)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), hcard]
  exact dvd_mul_of_dvd_left (by decide : 5 ∣ 60) _

/-- Transport to the specified Rudvalis carrier retains the original block and full Sylow. -/
theorem alternatingFiveDeleted_not_ru {G : Type*} [Group G] [Finite G]
    (e : G ≃* Rudvalis.Model) (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  exact alternatingFiveDeleted_not_ru_native
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap B) hB)
    ((map_mono hn).trans (B.le_normalizer_map e.toMonoidHom))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
