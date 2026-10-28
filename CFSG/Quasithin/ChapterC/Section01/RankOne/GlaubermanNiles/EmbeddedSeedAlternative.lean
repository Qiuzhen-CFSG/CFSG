module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalSeedAlternative

/-!
# The local-seed alternative through the actual embedding

C.1.18 applies to the original Baumann subgroup even when its local
residual join is represented as a subgroup of a selected overgroup.
The commuting embeddings retain the literal characteristic subgroup in G;
normality extends by the source normalizer generation. In the block case,
the injective image of the short residual feeds C.1.21 propagation.

Source: Aschbacher–Smith C.1.21(3), printed pp.128–129.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
open GlaubermanNiles
universe u v
variable {G : Type u} [Group G] [Finite G] {H : Type v} [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem normal_characteristic_image_of_embedding (S : Subgroup G)
    (e : S →* H) (i : H →* G) (hi : i.comp e=S.subtype)
    (D : Subgroup S) [D.Characteristic] (hn : (D.map e).Normal)
    (hgen : i.range ⊔ normalizer (S : Set G)=⊤) : (D.map S.subtype).Normal := by
  let := hn
  have hm : (D.map e).map i=D.map S.subtype := by rw [map_map,hi]
  have hH : i.range ≤ normalizer (D.map S.subtype : Set G) := by
    rw [←hm]
    have hh := (D.map e).le_normalizer_map i
    rw [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map] at hh
    exact hh
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  exact sup_le hH (normalizer_le_normalizer_characteristic_image S D)

theorem embedded_local_seed_alternative (S L : Subgroup G)
    (e : S →* H) (i : H →* G) (hinj : Function.Injective i) (hi : i.comp e=S.subtype)
    (hlocal : InLocalClass e) (D : CharacteristicPair S) (hD : D.Universal.{u,v})
    (hgen : i.range ⊔ normalizer (S : Set G)=⊤)
    (hYL : (pResidual 2 H).map i ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L=pCore 2 L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hQY : pCore 2 G ≤ normalizer ((pResidual 2 H).map i : Set G))
    (hne : ¬(((pResidual 2 H).map i).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤
      center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup S, C.Characteristic ∧ C≠⊥ ∧ (C.map S.subtype).Normal) ∨ IsBlock L := by
  rcases hD H e hlocal with hc | hn | hb
  · left
    let := D.first_characteristic
    exact ⟨D.first,inferInstance,D.first_ne_bot,normal_characteristic_image_of_embedding S e i hi _
      ((hlocal.first_normal_iff_central D.first D.first_le_omegaCenter).mpr hc) hgen⟩
  · left
    let := D.second_characteristic
    exact ⟨D.second,inferInstance,D.second_ne_bot,
      normal_characteristic_image_of_embedding S e i hi _ hn hgen⟩
  · right
    have hY : IsShort ((pResidual 2 H).map i) :=
      hb.1.short.of_mulEquiv ((pResidual 2 H).equivMapOfInjective i hinj)
    exact isBlock_of_short_seed _ L hYL hY hL hpL hfL hQY hne
end CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
