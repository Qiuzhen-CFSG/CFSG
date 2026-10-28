module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowReduction
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer
public import Stellmacher.BaumannMap
/-!
# Characteristic Baumann subgroups in the contrary-normalizer branch

Normalizer uniqueness for the original component--Sylow join excludes every
nonzero characteristic subgroup of Baum(T) that is normal in that join:
N(T) normalizes Baum(T) and hence normalizes its characteristic subgroups.
Injective Baumann transport gives the same exclusion on the literal Sylow
carrier inside LT. This is the characteristic alternative needed by C.1.24.

Source: Aschbacher--Smith, 3.3.6(c), printed p.587, and C.1.24, pp.130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.SylowNormalizer
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
lemma no_characteristic_baumann_normal (S : Setup T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup (ChapterB.baumann (T : Subgroup G))) [C.Characteristic]
    (hne : C ≠ ⊥) :
    ¬ L ⊔ (T : Subgroup G) ≤
      normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) := by
  intro hn
  apply hescape
  have hCB : C.map (ChapterB.baumann (T : Subgroup G)).subtype ≤
      L ⊔ (T : Subgroup G) :=
    (Subgroup.map_subtype_le C).trans (inf_le_left.trans le_sup_right)
  have hCne : C.map (ChapterB.baumann (T : Subgroup G)).subtype ≠ ⊥ := by
    intro he
    exact hne ((Subgroup.map_eq_bot_iff_of_injective C
      (ChapterB.baumann (T : Subgroup G)).subtype_injective).mp he)
  have hnB : normalizer (T : Set G) ≤
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
    rw [ChapterB.baumann, ChapterB.thompsonAlpha, ← Sylow.coe_coe]
    exact Stellmacher.normalizer_le_normalizer_baumann (T : Subgroup G)
  exact (hnB.trans (normalizer_le_normalizer_characteristic_image _ C)).trans
    (S.hypothesis.toHypothesis1221.normal_subgroup_normalizer_le
      S.chosen.sylow_normalizes_component hCB hCne hn)

private lemma characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro α x hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨e.symm (α (e c)), ?_, e.apply_symm_apply _⟩
  exact characteristic_iff_le_comap.mp inferInstance ((e.trans α).trans e.symm) hc

lemma no_characteristic_baumann_join (S : Setup T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (P : Sylow 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hP : (P : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = T)
    (C : Subgroup (ChapterB.baumann (P : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G))))
    [C.Characteristic] (hne : C ≠ ⊥) :
    ¬ (C.map (ChapterB.baumann (P : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G))).subtype).Normal := by
  let H := L ⊔ (T : Subgroup G)
  let B := ChapterB.baumann (P : Subgroup H)
  have hB : B.map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have hb := Stellmacher.baumann_map_injective H.subtype H.subtype_injective (P : Subgroup H)
    change (ChapterB.baumann (P : Subgroup H)).map H.subtype =
      ChapterB.baumann ((P : Subgroup H).map H.subtype) at hb
    rw [hP] at hb
    exact hb
  let e : B ≃* ChapterB.baumann (T : Subgroup G) :=
    (B.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hB)
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv e C
  have hDne : D ≠ ⊥ := fun hb => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hb)
  have hmap : (D.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf H =
      C.map B.subtype := by
    ext x
    constructor
    · rintro ⟨s, ⟨c, hc, hcs⟩, hsx⟩
      refine ⟨c, hc, ?_⟩
      apply Subtype.ext
      exact (congrArg (ChapterB.baumann (T : Subgroup G)).subtype hcs).trans hsx
    · rintro ⟨c, hc, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, rfl⟩
  have hle : D.map (ChapterB.baumann (T : Subgroup G)).subtype ≤ H :=
    (map_subtype_le _).trans (inf_le_left.trans le_sup_right)
  intro hn
  exact no_characteristic_baumann_normal S hescape D hDne
    ((normal_subgroupOf_iff_le_normalizer hle).mp (hmap.symm ▸ hn))

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.SylowNormalizer
