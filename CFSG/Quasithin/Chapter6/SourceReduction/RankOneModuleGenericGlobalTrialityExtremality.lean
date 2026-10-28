module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortSylow
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusionModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizerBounds

/-!
# Triality extremality through the original comparison

The local root reductions simultaneously retain model conjugacy and conjugacy
through the two compatible parabolic maps. For any supplied comparison, fusing
its marked roots would fuse all involutions of S, contradicting the previously
constructed pair of distinct ambient classes. Thus ambient fusion of involutions
in S reflects to conjugacy in the genuine model, with the supplied maps fixed.

Suppose C_U(v) is Sylow in the model centralizer, exactly the premise of F.4.40.
Reflection and faithful transport bound each C_T(x), for x conjugate to the
image of v, by |C_U(v)|. Choose an ambient conjugate with saturated centralizer
and apply Sylow comparison to conclude that C_T(v) itself is Sylow in C_G(v).
The original S=T is discharged from the source hypotheses. No homomorphism
from the whole model, nor a replacement of the supplied comparison, is used.

The Chapter 12 companion applies these statements to the actual chosen-module
pair. The designated short-root model extremality premise, F.4.42 full ambient
containment, and F.4.43 comparison with the genuine full-normalizer extension
remain necessary for recognition. The exact q¹⁰ count in the imported module
alone does not discharge those premises.

Source: Aschbacher--Smith F.4.35 and F.4.40, printed pp.292 and 294,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Internal imports reuse the local fusion
paths and faithful centralizer transport while preserving their boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.Centers
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityExtremality
open TrialityCompletionFusion
variable {G : Type*} [Group G]

private theorem inclusion_amalgam_inverse_agree
    {M : Type*} [Group M] (X Y : Subgroup G) (C B A : Subgroup M)
    (hBC : B ≤ C) (hBA : B ≤ A)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X (X ⊓ Y) Y inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups C B A hBC hBA))
    (x : M) (hx : x ∈ B) (hu : x ∈ A) (hv : x ∈ C) :
    (e.right.symm ⟨x,hu⟩).val = (e.left.symm ⟨x,hv⟩).val :=
  (congrArg Subtype.val (e.symm.right_commutes ⟨x,hx⟩)).trans
    (congrArg Subtype.val (e.symm.left_commutes ⟨x,hx⟩)).symm

private theorem compatible_class_pair (n : ℕ) (hn : 0 < n)
    (f : parabolic (binaryParameters n hn) .arms →* G)
    (l : parabolic (binaryParameters n hn) .central →* G)
    (ha : ∀ x ∈ borel (binaryParameters n hn), ∀ hx hy, f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (x : parabolic (binaryParameters n hn) .arms)
    (hx : x.val ∈ unipotent (binaryParameters n hn)) (hx2 : orderOf x = 2) :
    let P := binaryParameters n hn
    (IsConj (f (longElement P rfl)) (f x) ∧ IsConj (longElement P rfl).val x.val) ∨
      (IsConj (f (shortElement P rfl)) (f x) ∧ IsConj (shortElement P rfl).val x.val) := by
  let P := binaryParameters n hn
  have hlong : (longElement P rfl).val ∈ unipotent P :=
    highest_U P rfl (by rw [← highestHom_range P rfl]; exact ⟨_,rfl⟩)
  have hshort : (shortElement P rfl).val ∈ unipotent P := short_U P rfl 2 1
  rcases unipotent_fusion n hn ⟨x.val,hx⟩ ((Subgroup.orderOf_coe x).trans hx2) with
    ⟨z,hz,hc⟩ | ⟨t,ht,hc⟩
  · have hpath := (highest_one_fusion P rfl z hz).trans hc
    exact Or.inl ⟨hpath.map_conj f l ha hlong hx,
      hpath.map_conj (parabolic P .arms).subtype (parabolic P .central).subtype
        (fun _ _ _ _ => rfl) hlong hx⟩
  · have hpath := (short_one_fusion n hn t ht).trans hc
    exact Or.inr ⟨hpath.map_conj f l ha hshort hx,
      hpath.map_conj (parabolic P .arms).subtype (parabolic P .central).subtype
        (fun _ _ _ _ => rfl) hshort hx⟩

private theorem compatible_fusion_reflects (n : ℕ) (hn : 0 < n)
    (f : parabolic (binaryParameters n hn) .arms →* G)
    (l : parabolic (binaryParameters n hn) .central →* G)
    (ha : ∀ x ∈ borel (binaryParameters n hn), ∀ hx hy, f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (hnon : ¬ IsConj (f (longElement (binaryParameters n hn) rfl))
      (f (shortElement (binaryParameters n hn) rfl)))
    (x y : parabolic (binaryParameters n hn) .arms)
    (hx : x.val ∈ unipotent (binaryParameters n hn))
    (hy : y.val ∈ unipotent (binaryParameters n hn))
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : IsConj (f x) (f y)) : IsConj x.val y.val := by
  rcases compatible_class_pair n hn f l ha x hx hx2 with ⟨hfx,hmx⟩ | ⟨hfx,hmx⟩ <;>
    rcases compatible_class_pair n hn f l ha y hy hy2 with ⟨hfy,hmy⟩ | ⟨hfy,hmy⟩
  · exact hmx.symm.trans hmy
  · exact (hnon ((hfx.trans hxy).trans hfy.symm)).elim
  · exact (hnon ((hfy.trans hxy.symm).trans hfx.symm)).elim
  · exact hmx.symm.trans hmy

variable [Finite G]
private theorem compatible_saturation_transfer (n : ℕ) (hn : 0 < n)
    (f : parabolic (binaryParameters n hn) .arms →* G) (hf : Function.Injective f)
    (T : Sylow 2 G)
    (hS : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map f = (T : Subgroup G))
    (hreflection : ∀ x y : parabolic (binaryParameters n hn) .arms,
      x.val ∈ unipotent (binaryParameters n hn) →
      y.val ∈ unipotent (binaryParameters n hn) →
      orderOf x = 2 → orderOf y = 2 → IsConj (f x) (f y) → IsConj x.val y.val)
    (v : parabolic (binaryParameters n hn) .arms)
    (hv : v.val ∈ unipotent (binaryParameters n hn)) (hv2 : orderOf v = 2)
    (hmodel : ∃ R : Sylow 2 (centralizer ({v.val} : Set (Carrier (binaryParameters n hn)))),
      (R : Subgroup _) = (unipotent (binaryParameters n hn)).subgroupOf
        (centralizer ({v.val} : Set (Carrier (binaryParameters n hn))))) :
    ∃ R : Sylow 2 (centralizer ({f v} : Set G)),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({f v} : Set G)) := by
  let P := binaryParameters n hn
  let U := unipotent P
  let E := (T : Subgroup G) ⊓ centralizer ({f v} : Set G)
  have hcard : Nat.card E = Nat.card (U ⊓ centralizer ({v.val} : Set (Carrier P)) : Subgroup _) :=
    triality_centralizer_card_transport P f hf _ hS v
  have hUp : IsPGroup 2 U := (unipotentSylow P rfl).isPGroup'
  have hmaxmodel (D : Subgroup (Carrier P)) (hD : IsPGroup 2 D)
      (hED : U ⊓ centralizer ({v.val} : Set (Carrier P)) ≤ D)
      (hDC : D ≤ centralizer ({v.val} : Set (Carrier P))) :
      D = U ⊓ centralizer ({v.val} : Set (Carrier P)) := by
    obtain ⟨R,hR⟩ := hmodel
    have he := R.is_maximal' (hD.comap_subtype (K := centralizer ({v.val} : Set (Carrier P)))) (by
      rw [hR]
      intro x hx
      exact hED ⟨hx,x.property⟩)
    have hh := congrArg (fun V : Subgroup (centralizer ({v.val} : Set (Carrier P))) =>
      V.map (centralizer ({v.val} : Set (Carrier P))).subtype) he
    rw [hR] at hh
    change (D.subgroupOf (centralizer ({v.val} : Set (Carrier P)))).map _ =
      (U.subgroupOf (centralizer ({v.val} : Set (Carrier P)))).map _ at hh
    rw [map_subgroupOf_eq_of_le hDC,subgroupOf_map_subtype] at hh
    exact hh
  have hbound (x : T) (hvx : IsConj (f v) x.val) :
      Nat.card ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G) : Subgroup G) ≤ Nat.card E := by
    have hx : x.val ∈ ((unipotent P).subgroupOf (parabolic P .arms)).map f :=
      hS.ge (show x.val ∈ (T : Subgroup G) from x.property)
    obtain ⟨y,hy,he⟩ := hx
    have hy2 : orderOf y = 2 := by
      rw [← orderOf_injective f hf y,he]
      obtain ⟨g,hg⟩ := isConj_iff.mp hvx
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq (f v)).trans ((orderOf_injective f hf v).trans hv2)
    have hxy := hreflection v y hv hy hv2 hy2 (he.symm ▸ hvx)
    rw [← he,triality_centralizer_card_transport P f hf _ hS y,hcard]
    exact card_le_of_isConj_of_saturated_centralizer v.val y.val hxy
      (U ⊓ centralizer ({v.val} : Set (Carrier P))) (hUp.to_le inf_le_left)
      inf_le_right hmaxmodel _ (hUp.to_le inf_le_left) inf_le_right
  have hvT : f v ∈ (T : Subgroup G) := hS ▸ mem_map_of_mem f hv
  obtain ⟨x,hvx,hmax⟩ := T.exists_conjugate_with_saturated_centralizer ⟨f v,hvT⟩
  rw [map_subtype_centralizer_singleton] at hmax
  let C := centralizer ({f v} : Set G)
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  have hRC : Nat.card ((R : Subgroup C).map C.subtype) ≤ Nat.card E :=
    (card_le_of_isConj_of_saturated_centralizer x.val (f v) hvx.symm
      ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G))
      (T.isPGroup'.to_le inf_le_left) inf_le_right hmax _
      (R.isPGroup'.map _) (map_subtype_le _)).trans (hbound x hvx)
  refine ⟨R,(eq_of_le_of_card_ge hR ?_).symm⟩
  rw [← card_map_of_injective C.subtype_injective]
  have hEC : Nat.card ((T : Subgroup G).subgroupOf C) = Nat.card E := by
    rw [← card_map_of_injective C.subtype_injective,subgroupOf_map_subtype]
  exact hRC.trans_eq hEC.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityExtremality

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- The two pinned root images remain nonconjugate for every supplied
whole-overlap comparison, retaining that comparison's original endpoint maps. -/
theorem Preparation.triality_comparison_involution_nonfusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    ¬ IsConj (e.right.symm (longElement P rfl)).val
      (e.right.symm (shortElement P rfl)).val := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic P .central →* G := X.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have ha (x : Carrier P) (hx : x ∈ borel P) (hu : x ∈ parabolic P .arms)
      (hv : x ∈ parabolic P .central) : f ⟨x,hu⟩ = l ⟨x,hv⟩ := by
    exact TrialityExtremality.inclusion_amalgam_inverse_agree X Y
      (parabolic P .central) (borel P) (parabolic P .arms)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e x hx hu hv
  have hS := d.triality_right_unipotent_image h hH.1.1.2 P rfl e
  change ¬ IsConj (f (longElement P rfl)) (f (shortElement P rfl))
  intro hbad
  have hall (x : G) (hx : x ∈ sourceS L H) (hx2 : orderOf x = 2) :
      IsConj (f (longElement P rfl)) x := by
    obtain ⟨y,hy,rfl⟩ := hS.symm ▸ hx
    have hy2 : orderOf y = 2 := (orderOf_injective f hf y).symm.trans hx2
    rcases TrialityExtremality.compatible_class_pair m hm f l ha y hy hy2 with ⟨hc,_⟩ | ⟨hc,_⟩
    · exact hc
    · exact hbad.trans hc
  obtain ⟨e₀,z,v,hz,hv,_,hz2,hv2,hnon,_⟩ :=
    d.triality_completion_involution_classes h hH hp m hm (Or.inr ⟨e⟩)
  have hS₀ := d.triality_right_unipotent_image h hH.1.1.2 P rfl e₀
  have hzS : z.val ∈ sourceS L H := by
    apply hS₀.le
    exact ⟨longElement P rfl,
      highest_U P rfl (by rw [← highestHom_range P rfl]; exact ⟨_,rfl⟩),hz.symm⟩
  have hvS : v.val ∈ sourceS L H := by
    apply hS₀.le
    exact ⟨shortElement P rfl,short_U P rfl 2 1,hv.symm⟩
  exact hnon ((hall z.val hzS ((Subgroup.orderOf_coe z).trans hz2)).symm.trans
    (hall v.val hvS ((Subgroup.orderOf_coe v).trans hv2)))

/-- Ambient conjugacy of involutions in the common Sylow reflects to
conjugacy in the genuine model, through this exact original comparison. -/
theorem Preparation.triality_comparison_fusion_reflects
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (x y : parabolic (binaryParameters m hm) .arms)
    (hx : x.val ∈ unipotent (binaryParameters m hm))
    (hy : y.val ∈ unipotent (binaryParameters m hm))
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : IsConj (e.right.symm x).val (e.right.symm y).val) :
    IsConj x.val y.val := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic P .central →* G := X.subtype.comp e.left.symm.toMonoidHom
  have ha (a : Carrier P) (ha : a ∈ borel P) (hu : a ∈ parabolic P .arms)
      (hv : a ∈ parabolic P .central) : f ⟨a,hu⟩ = l ⟨a,hv⟩ :=
    TrialityExtremality.inclusion_amalgam_inverse_agree X Y
      (parabolic P .central) (borel P) (parabolic P .arms)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e a ha hu hv
  exact TrialityExtremality.compatible_fusion_reflects m hm f l ha
    (d.triality_comparison_involution_nonfusion h hH hp m hm e) x y hx hy hx2 hy2 hxy

/-- F.4.40 in the triality row: model extremality transfers to the actual
ambient centralizer through the same original comparison. S=T is proved,
and no ambient model embedding or full-normalizer extension is assumed. -/
theorem Preparation.triality_involution_centralizer_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (v : parabolic (binaryParameters m hm) .arms)
    (hv : v.val ∈ unipotent (binaryParameters m hm)) (hv2 : orderOf v = 2)
    (hmodel : ∃ R : Sylow 2 (centralizer ({v.val} : Set (Carrier (binaryParameters m hm)))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({v.val} : Set (Carrier (binaryParameters m hm))))) :
    let x : G := (e.right.symm v).val
    ∃ R : Sylow 2 (centralizer ({x} : Set G)),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({x} : Set G)) := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hS := (d.triality_right_unipotent_image h hH.1.1.2 P rfl e).trans
    (d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩))
  exact TrialityExtremality.compatible_saturation_transfer m hm f hf T hS
    (fun x y hx hy hx2 hy2 hxy =>
      d.triality_comparison_fusion_reflects h hH hp m hm e x y hx hy hx2 hy2 hxy)
    v hv hv2 hmodel

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
