module
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.LinearModels
public import Theory.Representation.BinaryPermutation.ProperInvariant
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# The two-core fixed subgroup in the whole terminal module

For a natural or augmentation module whose actor contains A₆, every
proper invariant subspace is fixed pointwise. Apply this to the image of
C_{U_H}(O₂(H)) in U_H/V₁. Its properness follows from the original seed
noncentrality, and relative normality makes its image invariant under H*.
Thus a critical quotient point that is not globally fixed cannot centralize
O₂(H). This proves the required movement without incorrectly extending
the seed centralizer identity to all of U_H. The cover constant line remains.

Source: Aschbacher--Smith, B.3.1 and the final point-parabolic argument of
13.8.1, printed pp.83,968--969.
-/
public section
open Subgroup BinaryPermutation Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
open IntersectionBalance Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- A proper invariant subspace of either whole-module model is fixed pointwise.
Only the actual actor embedding is used, including its alternating subgroup. -/
theorem LinearCoordinates.proper_invariant_fixed
    (a : SolvableExclusion.Five.StarAction H U Z)
    (e : Source.Hstar H →* S6) (hc : LinearCoordinates a e)
    (hAlt : A6 ≤ e.range)
    (W : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (hW : ∀ g v, v ∈ W → tildeRepresentation H U Z a g v ∈ W)
    (hp : W ≠ ⊤) :
    ∀ g v, v ∈ W → tildeRepresentation H U Z a g v = v := by
  rcases hc with ⟨f,he⟩ | ⟨f,he⟩
  · let Y := W.map f.toLinearMap
    have hY : ∀ g : A6, ∀ v ∈ Y, naturalRepresentation (Fin 6) g.val v ∈ Y := by
      rintro g _ ⟨v,hv,rfl⟩
      obtain ⟨b,hb⟩ := hAlt g.property
      exact ⟨tildeRepresentation H U Z a b v,hW b v hv,by simpa only [hb, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap] using he b v⟩
    have hpY : Y ≠ ⊤ := by
      intro ht
      apply hp
      apply top_unique
      intro v _
      obtain ⟨w,hw,heq⟩ := ht.ge (Submodule.mem_top : f v ∈ ⊤)
      exact f.injective heq ▸ hw
    have hzero := natural_invariant_eq_bot_of_ne_top (by decide) Y hY hpY
    intro g v hv
    have hv0 : f v = 0 := by
      have hh : f v ∈ Y := ⟨v,hv,rfl⟩
      simpa only [hzero, Submodule.mem_bot] using hh
    have hv0' : v = 0 := f.injective (hv0.trans (map_zero f).symm)
    rw [hv0',map_zero]
  · let Y := W.map f.toLinearMap
    have hY : ∀ g : A6, ∀ v ∈ Y, coreRepresentation (Fin 6) g.val v ∈ Y := by
      rintro g _ ⟨v,hv,rfl⟩
      obtain ⟨b,hb⟩ := hAlt g.property
      exact ⟨tildeRepresentation H U Z a b v,hW b v hv,by simpa only [hb, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap] using he b v⟩
    have hpY : Y ≠ ⊤ := by
      intro ht
      apply hp
      apply top_unique
      intro v _
      obtain ⟨w,hw,heq⟩ := ht.ge (Submodule.mem_top : f v ∈ ⊤)
      exact f.injective heq ▸ hw
    intro g v hv
    apply f.injective
    rw [he]
    exact core_proper_invariant_fixed (by decide) Y hY hpY (e g) (f v) ⟨v,hv,rfl⟩

/-- Properness of the O₂(H)-fixed subgroup forces its quotient image into
 the global fixed space; the possible cover constant line is not removed. -/
theorem core_fixed_image_fixed
    (a : SolvableExclusion.Five.StarAction H U Z)
    (hz : Z ≤ U) (hcentral : H ≤ centralizer (Z : Set G))
    (hproper : ¬ U ≤ centralizer (Source.QH H : Set G))
    (coords :
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom))
    (u : U) (hu : (u : G) ∈ centralizer (Source.QH H : Set G)) :
    ∀ g, a.action g (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U) u := by
  let C := U ⊓ centralizer (Source.QH H : Set G)
  let W := quotientSpace U Z C
  have hzC : Z ≤ C := le_inf hz (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hcentral))
  have hnQ : H ≤ normalizer (Source.QH H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp (by
      change (((pCore 2 H).map H.subtype).comap H.subtype).Normal
      rw [comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance)
  have hnC : H ≤ normalizer (C : Set G) :=
    (le_inf a.normalizes (hnQ.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hW : ∀ g v, v ∈ W → tildeRepresentation H U Z a g v ∈ W := by
    intro g v hv
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    obtain ⟨w,hw,rfl⟩ := hv
    let w' : U := ⟨(h : G) * (w : G) * (h : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalizes h.property) w).mp w.property⟩
    refine ⟨w', (mem_normalizer_iff.mp (hnC h.property) w).mp hw, ?_⟩
    exact (a.conjugation h w).symm
  have hp : W ≠ ⊤ := by
    intro ht
    apply hproper
    have hUC : U ≤ C ⊔ Z := le_sup_of_quotientSpace_le U Z U C le_rfl
      (by change quotientSpace U Z U ≤ W; rw [ht]; exact le_top)
    exact (hUC.trans_eq (sup_eq_left.mpr hzC)).trans inf_le_right
  have hfix : ∀ g v, v ∈ W → tildeRepresentation H U Z a g v = v := by
    rcases coords with ⟨e,he⟩ | ⟨e,he⟩
    · apply he.proper_invariant_fixed a _ _ W hW hp
      intro g hg
      exact ⟨e.symm ⟨g,hg⟩,by simp⟩
    · apply he.proper_invariant_fixed a _ _ W hW hp
      intro g _
      exact ⟨e.symm g,by simp⟩
  exact fun g => congrArg Additive.toMul
    (hfix g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) ⟨u,⟨u.property,hu⟩,rfl⟩)
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
