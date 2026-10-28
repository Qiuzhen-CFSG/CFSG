module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SstarConstruction

/-!
# Mutual normalization of the source Sylow actor and replacement radical

The original component Sylow is the intersection of the original full Sylow
with the normal component. The full Sylow normalizes this intersection and
the characteristic replacement. Restricting both statements to the actual
replacement overgroup gives the two normalization directions. In particular,
the literal cover seed U intersect C(S*) is normalized by the radical.

Source: MS93 (3.0),(3.4), pp.859,868, and the characteristic replacement in
Section7, p.933. The original full Sylow is retained as an explicit witness.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {J : Type*} [Group J] [Finite J] {L R : Subgroup J} [L.Normal]

omit [Finite J] in
theorem sourceSylow_isPGroup (d : CharacteristicReduction L R) (P : Sylow 2 L) :
    IsPGroup 2 (sourceSylow d P) := by
  rw [show sourceSylow d P = ((P : Subgroup L).map L.subtype).subgroupOf d.overgroup from
    SetLike.coe_injective (sourceSylow_coe d le_sup_left P)]
  exact (P.isPGroup'.map L.subtype).comap_subtype

omit [Finite J] in
theorem sourceSylow_normalizes_radical (d : CharacteristicReduction L R) (P : Sylow 2 L)
    (hPR : (P : Subgroup L).map L.subtype ≤ R) :
    sourceSylow d P ≤ normalizer (d.radical : Set d.overgroup) := by
  let := d.characteristic
  have hRU : R ≤ normalizer (d.ambient : Set J) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  have hmap := (comap_mono (hPR.trans hRU)).trans
    (d.ambient.le_normalizer_comap d.overgroup.subtype)
  rw [show sourceSylow d P = ((P : Subgroup L).map L.subtype).subgroupOf d.overgroup from
    SetLike.coe_injective (sourceSylow_coe d le_sup_left P)]
  exact hmap

theorem radical_normalizes_sourceSylow (d : CharacteristicReduction L R) (P : Sylow 2 J)
    (hP : (P : Subgroup J) = R) :
    d.radical ≤ normalizer (sourceSylow d (componentSylow L P) : Set d.overgroup) := by
  rw [show sourceSylow d (componentSylow L P) =
      (((componentSylow L P : Sylow 2 L) : Subgroup L).map L.subtype).subgroupOf d.overgroup from
    SetLike.coe_injective (sourceSylow_coe d le_sup_left _)]
  rw [componentSylow_coe]
  change d.radical ≤ normalizer (((P : Subgroup J).comap L.subtype |>.map L.subtype).comap d.overgroup.subtype : Set d.overgroup)
  rw [map_comap_eq,range_subtype,hP]
  have hn : R ≤ normalizer ((L ⊓ R : Subgroup J) : Set J) :=
    (le_inf (by rw [normalizer_eq_top]; exact le_top) R.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  exact (comap_mono ((map_subtype_le d.subgroup).trans hn)).trans
    ((L ⊓ R).le_normalizer_comap d.overgroup.subtype)

theorem radical_normalizes_cover_seed (d : CharacteristicReduction L R)
    (P : Sylow 2 J) (hP : (P : Subgroup J) = R)
    (U : Subgroup d.overgroup) [U.Normal] :
    d.radical ≤ normalizer
      ((U ⊓ centralizer (sourceSylow d (componentSylow L P) : Set d.overgroup) :
        Subgroup d.overgroup) : Set d.overgroup) := by
  have hcen : normalizer (sourceSylow d (componentSylow L P) : Set d.overgroup) ≤
      normalizer (centralizer (sourceSylow d (componentSylow L P) : Set d.overgroup) : Set d.overgroup) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  exact (le_inf (by rw [normalizer_eq_top]; exact le_top)
    ((radical_normalizes_sourceSylow d P hP).trans hcen)).trans
      inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
