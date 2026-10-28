module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicLocalClass
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# Propagating the original cubic seed in C.1.24

An overgroup of the ambient two-core has characteristic two. Its chosen
Sylow subgroup of index three and actual Thompson movement construct the
Glauberman--Niles local class. The Baumann image is retained literally, so
normalizer generation applies the same universal characteristic pair in G.
Its short residual then propagates to the original quasisimple component.

The local Sylow may be larger than the prescribed Baumann group; only their
Baumann images are identified. This is the source situation with
O₂(G)Baum(T), and does not assert O₂(G) ≤ Baum(T).

Source: Aschbacher--Smith, C.1.21(3--4) and C.1.24(a), printed pp.128--131.
The natural seven-letter selection is the intended application.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
open GlaubermanNiles GlaubermanArgument
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A constructed local action on the same Baumann group propagates its
characteristic pair or its short residual to the original component. -/
theorem selected_seed_block_alternative
    (R L H : Subgroup G) (hpR : IsPGroup 2 R)
    (hQH : pCore 2 G ≤ H)
    (P : Sylow 2 H)
    (hB : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann R)
    (hSne : ChapterB.baumann R ≠ ⊥)
    (hlocal : InLocalClass (inclusion
      (show ChapterB.baumann (P : Subgroup H) ≤
        pResidual 2 H ⊔ ChapterB.baumann (P : Subgroup H) from le_sup_right)))
    (hgen : H ⊔ normalizer (ChapterB.baumann R : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsBlock L := by
  let S := ChapterB.baumann R
  let B := ChapterB.baumann (P : Subgroup H)
  let K := pResidual 2 H ⊔ B
  let i : K →* G := H.subtype.comp K.subtype
  let Y := (pResidual 2 H).map H.subtype
  let E : B ≃* S := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)
  let e : S →* K := (inclusion (show B ≤ K from le_sup_right)).comp E.symm.toMonoidHom
  have he : i.comp e = S.subtype := by
    ext x
    exact congrArg (fun b : S => (b : G)) (E.apply_symm_apply x)
  have himage : i.range = Y ⊔ S := by
    rw [MonoidHom.range_comp, range_subtype, Subgroup.map_sup, hB]
  have hPN : (P : Subgroup H).map H.subtype ≤ normalizer (S : Set G) := by
    have hBN : (P : Subgroup H) ≤ normalizer (B : Set H) :=
      (P : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_baumann _)
    have hm := map_mono (f := H.subtype) hBN
    exact hm.trans ((B.le_normalizer_map H.subtype).trans_eq (congrArg (fun A : Subgroup G => normalizer (A : Set G)) hB))
  have hH : Y ⊔ (P : Subgroup H).map H.subtype = H := by
    rw [← Subgroup.map_sup, pResidual_sup_sylow_eq_top P, ← MonoidHom.range_eq_map, range_subtype]
  have hKgen : i.range ⊔ normalizer (S : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    refine sup_le ?_ le_sup_right
    exact hH.symm.le.trans (sup_le
      ((himage.symm ▸ le_sup_left).trans le_sup_left) (hPN.trans le_sup_right))
  have hres : (pResidual 2 K).map i = Y := by
    let C := (pResidual 2 H).subgroupOf K
    let D := B.subgroupOf K
    have hc : IsPPerfect 2 C := (isPPerfect_pResidual 2).of_surjective
      (subgroupOfEquivOfLe (show pResidual 2 H ≤ K from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show pResidual 2 H ≤ K from le_sup_left)).symm.surjective
    have hd : IsPGroup 2 D := (P.isPGroup'.to_le (show B ≤ P from inf_le_left)).comap_subtype
    have hsup : C ⊔ D = ⊤ := by
      rw [← subgroupOf_sup (show pResidual 2 H ≤ K from le_sup_left)
        (show B ≤ K from le_sup_right), subgroupOf_self]
    change (pResidual 2 K).map (H.subtype.comp K.subtype) = _
    rw [← map_map, pResidual_eq_of_isPPerfect_sup C D hc hd hsup,
      map_subgroupOf_eq_of_le (show pResidual 2 H ≤ K from le_sup_left)]
  have hQY : pCore 2 G ≤ normalizer (Y : Set G) :=
    hQH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  let : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hSne
  obtain ⟨D, hD⟩ := exists_universal_characteristicPair.{u,u}
    (hpR.to_le (show S ≤ R from inf_le_left)) (SymmetricSix.baumann_intrinsic_fixed R)
  exact embedded_local_seed_alternative S L e i
    (H.subtype_injective.comp K.subtype_injective) he (hlocal.precomp_equiv E.symm)
    D hD hKgen (hres.symm ▸ hYL) hL hpL hfL (hres.symm ▸ hQY) (hres.symm ▸ hne)


/-- The genuine index-three local action constructs its own local class,
then reconstructs every short-block clause of L in the block alternative. -/
theorem cubic_seed_block_alternative
    (R L H : Subgroup G) (hpR : IsPGroup 2 R)
    (hf : generalizedFitting G = pCore 2 G)
    (hQH : pCore 2 G ≤ H)
    (P : Sylow 2 H)
    (hB : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann R)
    (hindex : (P : Subgroup H).index = 3)
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) : Set H))
    (hgen : H ⊔ normalizer (ChapterB.baumann R : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsBlock L := by
  have hfitH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le H
        (by rw [← hf]; exact centralizer_generalizedFitting_le G) hQH)
  have hlocal := FiveBlockSource.cubic_omega_inLocalClass P hindex hfitH hmove
  have hSne : ChapterB.baumann R ≠ ⊥ := by
    intro hs
    have hb : ChapterB.baumann (P : Subgroup H) = ⊥ :=
      (map_eq_bot_iff_of_injective _ H.subtype_injective).mp (hB.trans hs)
    apply hmove
    apply (ChapterB.elementaryAbelianMaxJ_le_baumann (P : Subgroup H)).trans
    rw [hb]
    exact bot_le
  exact selected_seed_block_alternative R L H hpR hQH P hB hSne hlocal hgen
    hYL hL hpL hfL hne

end CFSG.Quasithin.ChapterC.RankOne.SevenSource
