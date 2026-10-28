module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CharacteristicNormal
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
/-!
# The external Baumann characteristic-subgroup block conclusion

Transport the same canonical pair from the original Baumann group to the
actual local Sylow. Each local normal alternative is normalized by both
the local group and the original Sylow, hence by their join. The original
no-characteristic-Baumann hypothesis therefore forces the selected A₅
block, with its original moved support and Thompson commutator.

Source: Aschbacher–Smith C.1.24(a), E.2.3(4), pp.130–131,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB GlaubermanNiles ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]
theorem external_normal_source_conclusion
    (T H : Subgroup G) (R : Sylow 2 H)
    (hBR : baumann T ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ T)
    (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann T)) (hD : D.Universal.{u,u}) :
    H ≤ normalizer (D.first.map (baumann T).subtype : Set G) ∨
      H ≤ normalizer (D.second.map (baumann T).subtype : Set G) ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L.map H.subtype = ⁅L.map H.subtype,elementaryAbelianMaxJ T⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) = ⁅U.map H.subtype,L.map H.subtype⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) ≤ U.map H.subtype) := by
  obtain ⟨E,hE,hfirst,hsecond,hC,hCE⟩ := external_pair_transport T H R hBR hRT D hD
  have hh := source_normal_alternatives R hfit L hcomp hprod eL U q hq hk hL p hp he hfix hJ E hE
  rcases hh with hn | hn | ⟨hb,ha,hcomm,hs,hU⟩
  · left
    let := hn
    have hh := (E.first.map (baumann (R : Subgroup H)).subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hfirst] using hh
  · right; left
    let := hn
    have hh := (E.second.map (baumann (R : Subgroup H)).subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hsecond,secondAmbient] using hh
  · right; right
    have hJmap : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype = elementaryAbelianMaxJ T := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      exact elementaryAbelianMaxJ_eq_of_intermediate T _
        ((elementaryAbelianMaxJ_le_baumann T).trans hBR) hRT
    refine ⟨hb,ha,?_,?_,?_⟩
    · have hm := congrArg (map H.subtype) hcomm
      rwa [map_commutator,hJmap] at hm
    · rw [←map_map,hs,map_commutator]
    · rw [←map_map]
      exact map_mono hU

theorem external_block_of_no_characteristic_baumann
    (T H : Subgroup G) (hT : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hgen : H ⊔ T = ⊤)
    (hno : ∀ D : Subgroup (baumann T), D.Characteristic → D ≠ ⊥ →
      ¬ (D.map (baumann T).subtype).Normal)
    (R : Sylow 2 H)
    (hBR : baumann T ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ T)
    (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    :
      IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L.map H.subtype = ⁅L.map H.subtype,elementaryAbelianMaxJ T⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) = ⁅U.map H.subtype,L.map H.subtype⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) ≤ U.map H.subtype := by
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} T hT hTne
  have hn (C : Subgroup (baumann T)) [C.Characteristic]
      (hH : H ≤ normalizer (C.map (baumann T).subtype : Set G)) :
      (C.map (baumann T).subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←hgen]
    exact sup_le hH ((T.le_normalizer.trans (normalizer_le_normalizer_baumann T)).trans
      (normalizer_le_normalizer_characteristic_image _ C))
  rcases external_normal_source_conclusion T H R hBR hRT hfit L hcomp hprod eL U q hq hk hL
      p hp he hfix hJ D hD with hf | hs | hb
  · let := D.first_characteristic
    exact (hno D.first D.first_characteristic D.first_ne_bot (hn D.first hf)).elim
  · let := D.second_characteristic
    exact (hno D.second D.second_characteristic D.second_ne_bot (hn D.second hs)).elim
  · exact hb
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
