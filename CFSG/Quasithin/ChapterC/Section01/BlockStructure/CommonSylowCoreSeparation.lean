module
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreConjugation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# A shared Sylow separates distinct centerless short-group layers

A two-group normalized by a centerless short group with core equal to its
moved layer meets that group trivially or in the entire layer. If two such
groups have the same Sylow subgroup, both intersections equal the intersection
with that Sylow. Distinct moved layers therefore force both intersections
to be trivial. The common Sylow need not be Sylow in any larger overgroup.

Source: the natural-block comparison in Aschbacher--Smith 10.2.3(4), p.747,
using the irreducibility in C.1.7.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

theorem IsShort.normalized_twoGroup_intersection
    {L : Subgroup G} (hL : IsShort L) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G))
    (hz : center L = ⊥) (hc : pCore 2 L = blockU L) :
    Q ⊓ L = ⊥ ∨ Q ⊓ L = (blockU L).map L.subtype := by
  let N := Q.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLQ
  have hp : IsPGroup 2 N := hQ.comap_of_injective L.subtype L.subtype_injective
  have hNU : N ≤ blockU L := hc ▸ (show N ≤ pCore 2 L from le_sSup ⟨inferInstance,hp⟩)
  have hlow : blockU L ⊓ center L ≤ N := by rw [hz,inf_bot_eq]; exact bot_le
  rcases hL.irreducible.2 N inferInstance hlow hNU with he | he
  · left
    simpa only [N,subgroupOf_map_subtype,hz,inf_bot_eq,bot_inf_eq,Subgroup.map_bot,inf_comm] using
      congrArg (map L.subtype) he
  · right
    simpa only [N,subgroupOf_map_subtype,inf_comm] using congrArg (map L.subtype) he

private theorem twoGroup_intersection_le_common_sylow
    (Q L S : Subgroup G) (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ normalizer (Q : Set G)) (hS : Chapter1.IsSylowIn 2 S L) :
    Q ⊓ L ≤ S := by
  obtain ⟨P,hP⟩ := hS
  let N := Q.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLQ
  have hp : IsPGroup 2 N := hQ.comap_of_injective L.subtype L.subtype_injective
  have hh := map_mono (f := L.subtype) (hp.le_sylow_of_normal P)
  simpa only [N,subgroupOf_map_subtype,hP,inf_comm] using hh

/-- Different moved layers in two centerless short groups sharing a Sylow
cannot meet any two-group normalized by both groups. -/
theorem short_pair_twoGroup_intersection_eq_bot
    (L K S Q : Subgroup G) (hL : IsShort L) (hK : IsShort K)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G))
    (hKQ : K ≤ normalizer (Q : Set G))
    (hzL : center L = ⊥) (hzK : center K = ⊥)
    (hcL : pCore 2 L = blockU L) (hcK : pCore 2 K = blockU K)
    (hSL : Chapter1.IsSylowIn 2 S L) (hSK : Chapter1.IsSylowIn 2 S K)
    (hne : (blockU L).map L.subtype ≠ (blockU K).map K.subtype) : Q ⊓ L = ⊥ := by
  have hSL' : S ≤ L := Chapter1.isSylowIn_iff.mp hSL |>.2.1
  have hSK' : S ≤ K := Chapter1.isSylowIn_iff.mp hSK |>.2.1
  have heL : Q ⊓ L = Q ⊓ S := le_antisymm
    (le_inf inf_le_left (twoGroup_intersection_le_common_sylow Q L S hQ hLQ hSL))
    (inf_le_inf_left Q hSL')
  have heK : Q ⊓ K = Q ⊓ S := le_antisymm
    (le_inf inf_le_left (twoGroup_intersection_le_common_sylow Q K S hQ hKQ hSK))
    (inf_le_inf_left Q hSK')
  rcases hL.normalized_twoGroup_intersection Q hQ hLQ hzL hcL with hb | he
  · exact hb
  rcases hK.normalized_twoGroup_intersection Q hQ hKQ hzK hcK with hb | he'
  · exact heL.trans (heK.symm.trans hb)
  · exact (hne (he.symm.trans (heL.trans (heK.symm.trans he')))).elim
end CFSG.Quasithin.ChapterC
