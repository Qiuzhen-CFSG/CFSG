module

public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.BinaryAlternatingSevenControl.Offenders
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.OmegaCenter
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.QuotientGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Image
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# Exceptional A₇ characteristic-normalizer control

This is the source proof of C.1.23(2) for an exceptional A₇ block. In the
literal product LT, the block centralizer theorem identifies the conjugation
quotient on U with a faithful four-dimensional binary A₇ action. The native
A₇ geometry gives its normal Sylow offender and generation by the offender
normalizer and the fixed-line kernel. The omega-center splitting then lifts
these generators to the characteristic normalizer of T. Finally the
inclusion LT ≤ G transports the closure back to G.

Source: Aschbacher–Smith, C.1.23(2), printed pp.129–130. The proof uses
the corrected fixed-line formulation; the printed direct-product plane
centralizer is not used.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open scoped IsMulCommutative Pointwise
universe u
variable {G : Type u} [Group G] [Finite G]

theorem product_control_native
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalA7Block L) (T : Sylow 2 G)
    (hp : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    (T : Subgroup G).characteristicNormalizerClosure = ⊤ := by
  have hres := pResidual_eq_of_subnormal_product L (T : Subgroup G)
    hL.subnormal hL.short.twoPerfect T.isPGroup' hp
  let : L.Normal := hres ▸ inferInstance
  let U := (blockU L).map L.subtype
  have hUn : U.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ normalizer (L : Set G) from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image L (blockU L))
  let := hUn
  let : IsElementaryAbelian 2 U := hm.1.elementary.map L.subtype
  let H := G ⧸ centralizer (U : Set G)
  let q : G →* H := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' _
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U q hq hk
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := ambient_finrank L hm
  obtain ⟨a⟩ := image_is_a7 L hm q hk
  let : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hN : L.map q = ⊤ := Representation.BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top ρ hf hd (L.map q) a
  let e : H ≃* alternatingGroup (Fin 7) :=
    ((Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).symm.trans
      (MulEquiv.subgroupCongr hN).symm).trans a
  let r : G →* alternatingGroup (Fin 7) := e.toMonoidHom.comp q
  have hr : Function.Surjective r := e.surjective.comp hq
  have hkr : r.ker = centralizer (U : Set G) :=
    (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hk
  have hLr : L.map r = ⊤ := by
    rw [show r = e.toMonoidHom.comp q from rfl, ← map_map, hN,
      map_top_of_surjective _ e.surjective]
  have hcore : centralizer (U : Set G) = pCore 2 G := lemma_C_1_11_single L hL T hp
  have hUcore : U ≤ pCore 2 G :=
    (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL.subnormal)
  have hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G :=
    (centralizer_le hUcore).trans hcore.le
  let σ := NormalElementaryQuotient.representation U r hr hkr
  have hσ : Function.Injective σ := NormalElementaryQuotient.representation_injective U r hr hkr
  obtain ⟨A,hAR,hA,huniq,hgen⟩ := Representation.BinaryAlternatingSevenControl.exists_unique_best_and_generation σ hσ hd (T.mapSurjective hr)
  exact control_of_quotient_generation L hL hm T le_normalizer_of_normal hchar hUn
    r hr hkr (hkr.trans hcore ▸ pCore_isPGroup.le_sylow_of_normal T) hLr A huniq hgen

theorem exceptionalA7_le_characteristicNormalizerClosure
    (T : Sylow 2 G) (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalA7Block L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    L ≤ (T : Subgroup G).characteristicNormalizerClosure := by
  let H := L ⊔ (T : Subgroup G)
  let D := L.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hD : IsBlock D := block_subgroupOf L H le_sup_left hL
  have hmD : IsExceptionalA7Block D := exceptional_subgroupOf L H le_sup_left hm
  have hp : ∀ x : H, ∃ d ∈ D, ∃ s ∈ (S : Subgroup H), d * s = x := by
    intro x
    have hx : (x : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G) hTL]
      exact x.property
    obtain ⟨d,hd,s,hs,he⟩ := hx
    exact ⟨⟨d,mem_sup_left hd⟩,hd,⟨s,mem_sup_right hs⟩,hs,Subtype.ext he⟩
  have hh := map_characteristicNormalizerClosure_le H.subtype H.subtype_injective (S : Subgroup H)
  have hmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  rw [product_control_native D hD hmD S hp, hmap, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact le_sup_left.trans hh

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
end
