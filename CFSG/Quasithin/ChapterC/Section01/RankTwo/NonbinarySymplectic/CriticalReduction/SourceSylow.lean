module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SstarConstruction

/-!
# The source Sylow actor on the minimum characteristic replacement

The original odd-index radical supplies an ambient Sylow that contains and
normalizes the original radical. Its intersection with the component is a
full component Sylow. Passing to the characteristic replacement retains
both normalization directions without transferring an odd-index radical
witness to the replacement.

Source: MS93 (3.0), (3.4), and Section 7, pp.859, 868, 932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- Choose the full source Sylow from the original odd-index overgroup. -/
theorem Input.exists_normalizing_sylow :
    ∃ P : Sylow 2 H, R ≤ (P : Subgroup H) ∧
      (P : Subgroup H) ≤ normalizer (R : Set H) := by
  obtain ⟨J,_,hodd,hR⟩ := h.radical
  let P : Sylow 2 J := Classical.choice inferInstance
  have hidx : ¬ 2 ∣ ((P : Subgroup J).map J.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul (by decide) P.not_dvd_index hodd.not_two_dvd_nat
  let S := (P.isPGroup'.map J.subtype).toSylow hidx
  have hJN : J ≤ normalizer (R : Set H) := by
    rw [← hR]
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  refine ⟨S,?_,(map_subtype_le _).trans hJN⟩
  change R ≤ (P : Subgroup J).map J.subtype
  rw [← hR]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal P)

/-- The original Sylow still contains and normalizes the characteristic cut. -/
theorem Input.exists_replacement_normalizing_sylow :
    ∃ P : Sylow 2 H, R ≤ (P : Subgroup H) ∧
      (P : Subgroup H) ≤ normalizer (R : Set H) ∧
      d.ambient ≤ (P : Subgroup H) ∧
      (P : Subgroup H) ≤ normalizer (d.ambient : Set H) := by
  obtain ⟨P,hRP,hPN⟩ := h.exists_normalizing_sylow
  let := d.characteristic
  exact ⟨P,hRP,hPN,(map_subtype_le d.subgroup).trans hRP,
    hPN.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)⟩

/-- A full Sylow of the unchanged component, inside the replacement, has
both normalization relations required of the source S-star. -/
theorem Input.exists_replacement_component_sylow :
    ∃ P : Sylow 2 (K.subgroupOf d.overgroup),
      d.radical ≤ normalizer
        (((P : Subgroup (K.subgroupOf d.overgroup)).map
          (K.subgroupOf d.overgroup).subtype) : Set d.overgroup) ∧
      ((P : Subgroup (K.subgroupOf d.overgroup)).map
          (K.subgroupOf d.overgroup).subtype) ≤ normalizer (d.radical : Set d.overgroup) := by
  let := h.component_normal
  obtain ⟨S,hRS,_,hTS,hSN⟩ := h.exists_replacement_normalizing_sylow d
  let P := Sp4Four.componentSylow K S
  let e := (subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left)).symm
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : ((P' : Subgroup (K.subgroupOf d.overgroup)).map
      (K.subgroupOf d.overgroup).subtype) =
      (K ⊓ (S : Subgroup H)).subgroupOf d.overgroup := by
    change ((P : Subgroup K).map e.toMonoidHom).map
      (K.subgroupOf d.overgroup).subtype = _
    rw [Sp4Four.componentSylow_coe]
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨z.property,hz⟩
    · rintro ⟨hk,hs⟩
      exact ⟨⟨x,hk⟩,⟨⟨x,hk⟩,hs,rfl⟩,rfl⟩
  refine ⟨P',?_,?_⟩
  · rw [hP]
    have hn : (S : Subgroup H) ≤ normalizer ((K ⊓ (S : Subgroup H)) : Set H) :=
      (le_inf (by rw [normalizer_eq_top]; exact le_top) S.le_normalizer).trans
        inf_normalizer_le_normalizer_inf
    exact (comap_mono (hTS.trans hn)).trans
      ((K ⊓ (S : Subgroup H)).le_normalizer_comap d.overgroup.subtype)
  · rw [hP]
    exact (comap_mono (inf_le_right.trans hSN)).trans
      (d.ambient.le_normalizer_comap d.overgroup.subtype)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
