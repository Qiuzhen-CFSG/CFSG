module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.OddNormalImage
public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.GroupTheory.PPerfectHom

/-!
# The quaternion image contradiction in F.6.16

A nontrivial two-perfect local image cannot lie in the preimage of the
two-core of the full image. F.6.7 therefore supplies both required local
intersection bounds for this literal preimage. F.6.8 makes it odd, while
the concrete ternary matrix calculation makes its image quaternion of
order eight. Consequently nontrivial local images in GL₂(3) must coincide.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Lemma F.6.16, printed pp.308–309 (1 March 2004 manuscript).
-/

public section

open Subgroup Matrix.GeneralLinearGroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

omit [Finite G] in
private theorem perfect_not_le_twoCore_preimage
    {D : Type*} [Group D] (f : G →* D) (A : Subgroup G)
    (hA : IsPPerfect 2 A) (hne : A.map f ≠ ⊥) :
    ¬ A ≤ (pCore 2 f.range).comap f.rangeRestrict := by
  intro hle
  let g : A →* pCore 2 f.range :=
    (f.rangeRestrict.comp A.subtype).codRestrict _ (fun x => hle x.property)
  have hg := hA.hom_eq_one_of_isPGroup pCore_isPGroup g
  apply hne
  apply eq_bot_iff.mpr
  rintro y ⟨x, hx, rfl⟩
  have hh : g (⟨x, hx⟩ : A) = 1 := DFunLike.congr_fun hg (⟨x, hx⟩ : A)
  exact mem_bot.mpr (congrArg (fun z : pCore 2 f.range => z.val.val) hh)

/-- The literal quaternion-core preimage is odd and maps onto a group of
order eight, an impossibility. Both local nontrivial images are retained. -/
theorem no_ternary_image_containing_specialLinear
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hS : threeSpecialLinear ≤ f.range)
    (h₁ : ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥)
    (h₂ : ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥) : False := by
  let W := (pCore 2 f.range).comap f.rangeRestrict
  have hW₁ : G₁ ⊓ W ≤ (pCore 2 G₁).map G₁.subtype :=
    (h.left_subnormal_core_iff_not_residual_le W
      (Normal.isSubnormal inferInstance)).mpr
      (perfect_not_le_twoCore_preimage f _ (isPPerfect_embedded_pResidual 2 G₁) h₁)
  have hW₂ : G₂ ⊓ W ≤ (pCore 2 G₂).map G₂.subtype :=
    (h.right_subnormal_core_iff_not_residual_le W
      (Normal.isSubnormal inferInstance)).mpr
      (perfect_not_le_twoCore_preimage f _ (isPPerfect_embedded_pResidual 2 G₂) h₂)
  have hodd := odd_card_image_of_local_intersections h hcore W f.rangeRestrict hW₁ hW₂
  have hmap : W.map f.rangeRestrict = pCore 2 f.range :=
    map_comap_eq_self_of_surjective f.rangeRestrict_surjective _
  rw [hmap, three_twoCore_card f.range hS] at hodd
  norm_num at hodd

/-- Distinct nontrivial local two-residual images cannot occur in GL₂(3).
This is the final contradiction in the non-three-group branch of F.6.16. -/
theorem ternary_local_residual_images_eq
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (h₁ : ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥)
    (h₂ : ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥) :
    ((pResidual 2 G₁).map G₁.subtype).map f =
      ((pResidual 2 G₂).map G₂.subtype).map f := by
  by_contra hne
  have hP (M : Subgroup G) : IsPPerfect 2 (((pResidual 2 M).map M.subtype).map f) :=
    (isPPerfect_embedded_pResidual 2 M).of_surjective
      (f.subgroupMap _) (f.subgroupMap_surjective _)
  have hgen := three_distinct_twoPerfect_join _ _ (hP G₁) (hP G₂) h₁ h₂ hne
  apply no_ternary_image_containing_specialLinear h hcore f _ h₁ h₂
  rw [← hgen]
  exact sup_le (map_le_range _ _) (map_le_range _ _)

end CFSG.Quasithin.ChapterF.Noncyclic
