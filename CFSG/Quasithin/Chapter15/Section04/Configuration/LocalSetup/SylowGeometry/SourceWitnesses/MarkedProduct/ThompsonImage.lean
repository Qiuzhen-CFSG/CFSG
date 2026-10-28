module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.QuotientCoordinates

/-!
# Source hypotheses for Baumann’s argument

Maximum elementary replacement forces an independent sign in the original Thompson image. Its T-conjugate supplies the other sign; the image is therefore the order-four Sylow subgroup in the fixed-plane base, as needed for the two conjugate Thompson groups in Baumann’s argument.

Source: Aschbacher–Smith, B.2.18 and15.4.12(4–6), pp.81 and1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]
theorem SourceAction.exists_independent_thompson_parity
    {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}
    (d : SourceAction T M X) (h : Input K T M X 2) :
    ∃ b : (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M,
      (codeEquiv.symm (d.actor b)).1.2 ≠ (codeEquiv.symm (d.actor b)).2.1.2 := by
  by_contra! hp
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  let W' := W.subgroupOf (T : Subgroup G)
  let e : W' ≃* W := subgroupOfEquivOfLe hWT
  let : W'.Normal := normal_subgroupOf_of_le_normalizer (h.sylow_le.trans h.moved_normalized)
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.subgroupOf hWT
  let a : Action W' :=
    { coordinates := e.trans d.coordinates
      actor := d.actor.comp (inclusion h.sylow_le)
      intertwines := by
        intro g w
        apply Subtype.ext
        exact d.intertwines (inclusion h.sylow_le g) (e w) }
  have hJmap : (elementaryAbelianMaxJ (⊤ : Subgroup (T : Subgroup G))).map (T : Subgroup G).subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    have he := elementaryAbelianMaxJ_map_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective (⊤ : Subgroup (T : Subgroup G))
    simpa only [←MonoidHom.range_eq_map, range_subtype] using he.symm
  have hkill := thompson_killed_of_equal_parity a (fun j hj => by
    have hh : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
      hJmap ▸ (mem_map.mpr ⟨j,hj,rfl⟩)
    exact hp ⟨inclusion h.sylow_le j,hh⟩)
  apply d.thompson_image_ne_bot h
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro m hm
  obtain ⟨j,hj,hjm⟩ := hJmap.symm.le hm
  have he : inclusion h.sylow_le j = m := Subtype.ext hjm
  change d.actor m = 1
  rw [←he]
  exact hkill hj


theorem SourceAction.thompson_image_card
    {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}
    (d : SourceAction T M X) (h : Input K T M X 2) :
    Nat.card (((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M).map d.actor) = 4 := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let D := (J.subgroupOf M).map d.actor
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun A hA => hA.1
  have hJS : J ≤ ChapterB.baumann (T : Subgroup G) := by
    refine le_inf hJT ?_
    intro j hj z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hD : D ≤ base := by
    rintro _ ⟨j,hj,rfl⟩
    exact d.baumann_base (hJS hj)
  have hDp : IsPGroup 2 D := (T.isPGroup'.to_le hJT).comap_subtype.map d.actor
  have hrp : IsPGroup 3 rotations := IsPGroup.of_card (n := 2) Concrete.rotations_card
  have hd : Disjoint rotations D := IsPGroup.disjoint_of_ne 3 2 (by decide) _ _ hrp hDp
  obtain ⟨b,hb⟩ := d.exists_independent_thompson_parity h
  obtain ⟨t,ht⟩ := d.exists_swap h
  let m := inclusion h.sylow_le t
  have hnJ : (t : G) ∈ normalizer (J : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj (t : G)).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv]
    exact congrArg elementaryAbelianMaxJ
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property))
  have hconj : d.actor m * d.actor b * (d.actor m)⁻¹ ∈ D := by
    refine mem_map.mpr ⟨m*b*m⁻¹,(mem_normalizer_iff.mp hnJ (b : G)).mp b.property,?_⟩
    rw [map_mul,map_mul,map_inv]
  have hgen : rotations ⊔ D = base := by
    apply Concrete.base_generated_of_independent_parity _ (sup_le Concrete.rotations_le_base hD)
      le_sup_left (d.actor b) (d.actor m)
      ((le_sup_right : D ≤ rotations ⊔ D) ⟨b,b.property,rfl⟩) hb ht
      ((le_sup_right : D ≤ rotations ⊔ D) hconj)
  have hbcard : Nat.card base = 36 := by
    rw [Nat.card_congr Concrete.baseEquiv.toEquiv,Nat.card_prod]
    norm_num [Concrete.S3,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes rotations D le_normalizer_of_normal
  rw [Concrete.rotations_card, disjoint_iff.mp hd, card_bot, hgen, hbcard] at hc
  change Nat.card D = 4
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9) hc

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
