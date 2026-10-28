module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.BlockSelection

/-!
# The normal-subgroup obstruction for the original maximal intersection

A nontrivial characteristic subgroup of the Baumann subgroup of T ∩ I is
normalized by N_T(T ∩ I). If it is also normal in I, its two-local normalizer
is another member of the same outside family. The normalizer condition in
T contradicts maximality of T ∩ I. This discharges the normal alternative
in C.1.24 on the literal generated group, without a pushing-up assumption
on its Sylow subgroup.

Source: Aschbacher--Smith, 14.6.4 and C.1.24, pp.1025 and130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
variable {G : Type*} [Group G] [Finite G]

theorem no_normal_characteristic_baumann
    (T : Sylow 2 G) (Tu M Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (D : Subgroup (ChapterB.baumann (P : Subgroup I)))
    (hD : D.Characteristic) (hne : D ≠ ⊥) :
    ¬ (D.map (ChapterB.baumann (P : Subgroup I)).subtype).Normal := by
  let S := (T : Subgroup G) ⊓ I
  let B := ChapterB.baumann (P : Subgroup I)
  let E := D.map B.subtype
  let W := E.map I.subtype
  let := hD
  have hWne : W ≠ ⊥ := by
    intro hh
    exact hne ((D.map_eq_bot_iff_of_injective B.subtype_injective).mp
      ((E.map_eq_bot_iff_of_injective I.subtype_injective).mp hh))
  have hWp : IsPGroup 2 W :=
    (((P.isPGroup'.to_le (show B ≤ P from inf_le_left)).to_subgroup D).map B.subtype).map I.subtype
  have hSN : normalizer (S : Set G) ≤ normalizer (W : Set G) := by
    let e : B ≃* ChapterB.baumann S :=
      (B.equivMapOfInjective I.subtype I.subtype_injective).trans
        (MulEquiv.subgroupCongr (by
          change ((P : Subgroup I) ⊓ centralizer
            (omegaOneCenterAmbient (elementaryAbelianMaxJ (P : Subgroup I)) : Set I)).map
              I.subtype = _
          rw [baumann_map_injective I.subtype I.subtype_injective, hP]
          rfl))
    let F := D.map e.toMonoidHom
    let : F.Characteristic := by
      apply characteristic_iff_le_comap.mpr
      intro a x hx
      obtain ⟨y,hy,rfl⟩ := hx
      refine ⟨(MulAut.congr e.symm a) y,
        characteristic_iff_le_comap.mp hD (MulAut.congr e.symm a) hy,?_⟩
      exact e.apply_symm_apply (a (e y))
    have hm : F.map (ChapterB.baumann S).subtype = W := by
      change (D.map e.toMonoidHom).map (ChapterB.baumann S).subtype =
        (D.map B.subtype).map I.subtype
      rw [map_map,map_map]
      rfl
    rw [← hm]
    exact (normalizer_le_normalizer_baumann S).trans
      (normalizer_le_normalizer_characteristic_image _ F)
  intro hn
  let : E.Normal := hn
  have hIN : I ≤ normalizer (W : Set G) := by
    have hh := E.le_normalizer_map I.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hNW : normalizer (W : Set G) ∈ outsideOvergroups (Chapter1.H G) Tu Mc M :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨W,hWne,hWp,rfl⟩,
      hI.1.2.1.trans hIN, fun hh => hI.1.2.2.1 (hIN.trans hh),
      fun hh => hI.1.2.2.2 (hIN.trans hh)⟩
  have hbound : (T : Subgroup G) ⊓ normalizer (W : Set G) ≤ S :=
    hI.2 hNW (le_inf inf_le_left (inf_le_right.trans hIN))
  have hSproper : S.subgroupOf (T : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact hproper.not_ge
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (S.subgroupOf (T : Subgroup G)) hSproper)
  have htN : (t : G) ∈ normalizer (S : Set G) := by
    rw [← subgroupOf_normalizer_eq (show S ≤ (T : Subgroup G) from inf_le_left)] at ht
    exact ht
  exact htS (hbound ⟨t.property,hSN htN⟩)

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
