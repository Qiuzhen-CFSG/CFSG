module
public import CFSG.Quasithin.Chapter14.Section02.NormalBorel
public import CFSG.Quasithin.Chapter14.Section02.NormalAmalgam

/-!
# The literal normal-branch crossed Borel

Transport the intrinsic normal-Bender Borel through H's actual inclusion.
Its ambient image is M intersection K₁. It normalizes Y and its two-core,
and by definition normalizes T intersection K₁; hence it normalizes the
literal YS₂ required by F.1.1(d).

Source: Aschbacher--Smith 14.2.11 and the paragraph after 14.2.14,
printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem map_borel {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (K S : Subgroup A) :
    (ChapterF.Source.borel K S).map f = ChapterF.Source.borel (K.map f) (S.map f) := by
  unfold ChapterF.Source.borel
  rw [←Subgroup.map_inf _ _ _ hf]
  symm
  rw [←map_comap_eq_self
    (show K.map f ⊓ normalizer ((S ⊓ K).map f : Set B) ≤ f.range from
      inf_le_left.trans (K.map_le_range f))]
  rw [comap_inf,comap_normalizer_eq_of_le_range ((S ⊓ K).map_le_range f),
    comap_map_eq_self_of_injective hf,comap_map_eq_self_of_injective hf]

theorem source_normal_borel_cross
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    let Y := sourceResidual M Mc
    let K₁ := K.map H.subtype
    let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
    ChapterF.Source.borel K₁ (T : Subgroup G) = M ⊓ K₁ ∧
      ChapterF.Source.borel K₁ (T : Subgroup G) ≤ normalizer (Y ⊔ R : Subgroup G) := by
  let Y := sourceResidual M Mc
  let K₁ := K.map H.subtype
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax TH hP :=
    ChapterB.minimalParabolicMax_unique TH hP hN (fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hid := congrArg (Subgroup.map H.subtype) (normal_bender_borel_eq_overlap TH hP K hgen hq)
  rw [map_borel _ H.subtype_injective,←hmax,Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le inf_le_left,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hid
  have hb : ChapterF.Source.borel K₁ (T : Subgroup G) = M ⊓ K₁ := by
    change ChapterF.Source.borel K₁ (T : Subgroup G) = (H ⊓ M) ⊓ K₁ at hid
    rw [hid]
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (le_inf (inf_le_right.trans (map_subtype_le K)) inf_le_left) inf_le_right)
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc)
  have hCY := (hb.le.trans inf_le_left).trans hMY
  have hCR : ChapterF.Source.borel K₁ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (hCY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
      inf_le_right).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact ⟨hb,(le_inf hCY hCR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)⟩
end CFSG.Quasithin.Chapter14.Section02
