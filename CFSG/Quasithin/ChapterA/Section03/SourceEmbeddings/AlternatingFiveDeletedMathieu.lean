module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Mathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement

/-!
# Full-Sylow deleted-five exclusion in the Mathieu models

The characteristic layer of a deleted alternating-five block has order
sixteen. Its intrinsic Mathieu normalizer excludes that same block as a
local C-component at every full Sylow. The original Sylow normalizes the
characteristic layer, so restriction supplies exactly the forbidden local
configuration. Transport retains the original block and full Sylow under
the specified carrier isomorphism; no full normalizer-control assumption
or Sylow-order bound is needed.

Source: Aschbacher–Smith A.3.14, the M22 and M23 rows, using the intrinsic
local geometry developed for 2.4.25 and H.14.2–3.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem deleted_not_local_of_normalizer_obstruction
    (S : Sylow 2 H) (B : Subgroup H)
    (hlocal : B ∈ localCComponents S)
    (hn : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hbad : ∀ P : Sylow 2 (normalizer ((blockU B).map B.subtype : Set H)),
      B.subgroupOf (normalizer ((blockU B).map B.subtype : Set H)) ∉
        localCComponents P) : False := by
  let N := normalizer ((blockU B).map B.subtype : Set H)
  have hBN : B ≤ N := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hSN : (S : Subgroup H) ≤ N := hn.trans
    (normalizer_le_normalizer_characteristic_image B (blockU B))
  exact hbad (S.subtype hSN) (local_restrict hlocal hBN)

theorem alternatingFiveDeleted_not_m22_native
    (S : Sylow 2 Sporadic.Mathieu.M22) (B : Subgroup Sporadic.Mathieu.M22)
    (hB : IsAlternatingBlock B 5) (hlocal : B ∈ localCComponents S)
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (B : Set Sporadic.Mathieu.M22)) :
    False := by
  have hc : Nat.card ((blockU B).map B.subtype) = 16 :=
    (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  exact deleted_not_local_of_normalizer_obstruction S B hlocal hn
    (Chapter2.AlternatingTerminal.m22_normalizer_obstruction B hB hc).2.2

theorem alternatingFiveDeleted_not_m23_native
    (S : Sylow 2 Sporadic.Mathieu.M23) (B : Subgroup Sporadic.Mathieu.M23)
    (hB : IsAlternatingBlock B 5) (hlocal : B ∈ localCComponents S)
    (hn : (S : Subgroup Sporadic.Mathieu.M23) ≤ normalizer (B : Set Sporadic.Mathieu.M23)) :
    False := by
  have hc : Nat.card ((blockU B).map B.subtype) = 16 :=
    (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  exact deleted_not_local_of_normalizer_obstruction S B hlocal hn
    (Chapter2.AlternatingTerminal.m23_normalizer_obstruction B hB hc).2.2

private theorem deleted_no_model_of_equiv
    {M : Type*} [Group M] (e : H ≃* M)
    (hbad : ∀ (S : Sylow 2 M) (B : Subgroup M), IsAlternatingBlock B 5 →
      B ∈ localCComponents S → (S : Subgroup M) ≤ normalizer (B : Set M) → False)
    (S : Sylow 2 H) (B : Subgroup H) (hB : IsAlternatingBlock B 5)
    (hlocal : B ∈ localCComponents S) (hn : (S : Subgroup H) ≤ normalizer (B : Set H)) :
    False := by
  let := Finite.of_equiv H e.toEquiv
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  apply hbad (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap B) hB)
  · exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom
  · exact (map_mono hn).trans (B.le_normalizer_map e.toMonoidHom)

/-- The specified M22 carrier cannot contain the original normalized local deleted block. -/
theorem alternatingFiveDeleted_not_m22 (e : H ≃* Sporadic.Mathieu.M22)
    (S : Sylow 2 H) (B : Subgroup H) (hB : IsAlternatingBlock B 5)
    (hlocal : B ∈ localCComponents S) (hn : (S : Subgroup H) ≤ normalizer (B : Set H)) :
    False :=
  deleted_no_model_of_equiv e alternatingFiveDeleted_not_m22_native S B hB hlocal hn

/-- The specified M23 carrier cannot contain the original normalized local deleted block. -/
theorem alternatingFiveDeleted_not_m23 (e : H ≃* Sporadic.Mathieu.M23)
    (S : Sylow 2 H) (B : Subgroup H) (hB : IsAlternatingBlock B 5)
    (hlocal : B ∈ localCComponents S) (hn : (S : Subgroup H) ≤ normalizer (B : Set H)) :
    False :=
  deleted_no_model_of_equiv e alternatingFiveDeleted_not_m23_native S B hB hlocal hn

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
