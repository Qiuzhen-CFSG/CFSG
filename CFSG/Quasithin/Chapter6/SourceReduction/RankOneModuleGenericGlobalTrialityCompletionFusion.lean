module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCoreKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialTransfer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair

/-!
# Ambient triality involution classes and fusion in the actual factor join

Let K = O²(H), S = O₂(N_G(L) ∩ H), and J = L ∨ K. Both source
parabolics lie in this literal J. Their inverse comparison maps agree on the
whole overlap, so the model's local conjugation paths transport into J. They
cover all involutions of S by the highest-long-root and marked-short-root
classes, retaining the same actual arms-parabolic map.

The long representative lies in Z(K); the short representative is exactly the
witness from the all-degree nonfusion theorem. Hence their images remain
nonconjugate in G, and J realizes every ambient fusion between involutions
of S. Cyclic quotient transfer then covers every ambient involution by the
same two marked classes. This argument does not require S = T or odd degree.

These are the involution comparisons needed by the triality centralizer and
Thompson-order steps. Original uniqueness, exhaustive amalgam selection and
ambient model recognition remain with the generic-global assembly. The
Chapter 12 companion supplies the literal chosen-module application.

Source: Aschbacher–Smith F.4.35, F.4.38 and F.4.43, printed pp.292,294,296,
and 5.3.3–4, p.659 (`refs/quasithin.pdf`). The internal import reuses the
original root-pair marking and center transport without changing its API.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.Centers
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem triality_parabolics_le_join {L K S : Subgroup G} (hSK : S≤K) :
    (ChapterF.Source.parabolic ![L,K] S 0 ≤ L⊔K) ∧
    (ChapterF.Source.parabolic ![L,K] S 1 ≤ L⊔K) := by
  constructor
  · change L⊔S⊔ChapterF.Source.borel K S ≤ L⊔K
    exact sup_le (sup_le le_sup_left (hSK.trans le_sup_right)) (inf_le_left.trans le_sup_right)
  · change K⊔S⊔ChapterF.Source.borel L S ≤ L⊔K
    exact sup_le (sup_le le_sup_right (hSK.trans le_sup_right)) (inf_le_left.trans le_sup_left)

private theorem triality_longElement_order (P : Parameters) (hp : P.prime = 2) :
    orderOf (TrialityCompletionFusion.longElement P hp) = 2 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  rw [←orderOf_injective (parabolic P .arms).subtype Subtype.val_injective]
  apply orderOf_eq_prime
  · change (highestHom P hp (Multiplicative.ofAdd 1))^2=1
    rw [pow_two,←map_mul]
    change highestHom P hp (Multiplicative.ofAdd ((1:fixedField P)+1))=1
    rw [CharTwo.add_self_eq_zero]
    exact map_one (highestHom P hp)
  · change highestHom P hp (Multiplicative.ofAdd 1)≠1
    intro hh
    have he : Multiplicative.ofAdd (1 : fixedField P) = 1 :=
      highestHom_injective P hp (hh.trans (map_one (highestHom P hp)).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd he)

/-- The involutions of the original S have two marked classes in the actual
factor join. The two classes remain distinct under ambient conjugacy. -/
theorem Preparation.triality_completion_involution_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (TrialityCompletionFusion.longElement (binaryParameters m hm) rfl)).val ∧
        v.val = (e.right.symm (TrialityCompletionFusion.shortElement (binaryParameters m hm) rfl)).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        ∀ x : (L ⊔ residual H : Subgroup G), x.val∈sourceS L H → orderOf x=2 →
          IsConj z x ∨ IsConj v x := by
  obtain ⟨e,v₀,_,⟨w,hwv,hw⟩,_,hv2,hnot⟩ := d.triality_short_root_not_fused h hH hp m hm he
  let P := binaryParameters m hm
  have hSK : sourceS L H ≤ residual H := d.triality_sourceS_le_factors h hH.1.1.2 hp m hm he 1
  obtain ⟨hX,hY⟩ := triality_parabolics_le_join hSK
  let J := L ⊔ residual H
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* J := (inclusion hY).comp e.right.symm.toMonoidHom
  let l : parabolic P .central →* J := (inclusion hX).comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := (inclusion_injective hY).comp e.right.symm.injective
  have ha (x : Carrier P) (hx : x∈borel P) (hu : x∈parabolic P .arms)
      (hv : x∈parabolic P .central) : f ⟨x,hu⟩=l ⟨x,hv⟩ := by
    apply Subtype.ext
    let b : borel P := ⟨x,hx⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  let z : J := f (TrialityCompletionFusion.longElement P rfl)
  let v : J := f (TrialityCompletionFusion.shortElement P rfl)
  have hv : v.val=v₀ := by
    have hh : e.right w=TrialityCompletionFusion.shortElement P rfl := Subtype.ext hw
    have hh' := congrArg e.right.symm hh
    rw [e.right.symm_apply_apply] at hh'
    exact (congrArg Subtype.val hh').symm.trans hwv
  have hz : z.val∈(center (residual H)).map (residual H).subtype := by
    have hZ := (triality_comparison_images d h hH.1.1.2 hp P rfl e).1
    rw [←hZ]
    refine ⟨Multiplicative.ofAdd (1 : fixedField P),?_⟩
    change (e.right.symm (TrialityRootPair.longHom P rfl 2 (Multiplicative.ofAdd 1))).val=
      (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
    apply congrArg (fun x => (e.right.symm x).val)
    exact Subtype.ext (TrialityRootPair.long_two_eq P rfl 1)
  have hz2 : orderOf z=2 :=
    (orderOf_injective f hf _).trans (triality_longElement_order P rfl)
  have hv2' : orderOf v=2 := (Subgroup.orderOf_coe v).symm.trans (hv.symm ▸ hv2)
  refine ⟨e,z,v,rfl,rfl,hz,hz2,hv2',?_,?_⟩
  · intro hc
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    apply hnot g
    rw [←hv]
    exact ⟨z.val,hz,by change g*z.val*g⁻¹=v.val; exact hg⟩
  · intro x hx hx2
    let y : Y := ⟨x.val,(show sourceS L H≤Y from le_sup_right.trans le_sup_left) hx⟩
    have hyU : (e.right y).val∈unipotent P := by
      have hU := d.triality_right_unipotent_image h hH.1.1.2 P rfl e
      have hx' := hU.ge hx
      obtain ⟨a,haU,ha⟩ := hx'
      have hay : e.right.symm a=y := Subtype.ext ha
      have hya : a=e.right y := by rw [←hay,e.right.apply_symm_apply]
      exact hya ▸ haU
    have hy2 : orderOf (e.right y)=2 := by
      rw [e.right.orderOf_eq,←Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_coe x).trans hx2
    have hh := TrialityCompletionFusion.compatible_involution_classes m hm f l ha (e.right y) hyU hy2
    have hfx : f (e.right y)=x := by
      change inclusion hY (e.right.symm (e.right y))=x
      rw [e.right.symm_apply_apply]
      rfl
    rwa [hfx] at hh

/-- All ambient involutions lie in these two distinct marked classes. The
cyclic quotient transfer uses the original cubic-field arms action. -/
theorem Preparation.triality_ambient_involution_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (TrialityCompletionFusion.longElement (binaryParameters m hm) rfl)).val ∧
        v.val = (e.right.symm (TrialityCompletionFusion.shortElement (binaryParameters m hm) rfl)).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        (∀ x : (L ⊔ residual H : Subgroup G), x.val∈sourceS L H → orderOf x=2 →
          IsConj z x ∨ IsConj v x) ∧
        (∀ x : G, orderOf x=2 → IsConj z.val x ∨ IsConj v.val x) := by
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hnot,hclasses⟩ :=
    d.triality_completion_involution_classes h hH hp m hm he
  refine ⟨e,z,v,hz,hv,hzK,hz2,hv2,hnot,hclasses,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := d.triality_involution_fused_into_sourceS h hH.1.1.2 hp m hm he x hx
  let J := L⊔residual H
  have hSJ : sourceS L H≤J :=
    (d.triality_sourceS_le_factors h hH.1.1.2 hp m hm he 1).trans le_sup_right
  let a : J := ⟨y,hSJ hy⟩
  have ha2 : orderOf a=2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    exact (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq x).trans hx)
  rcases hclasses a hy ha2 with hz | hv
  · exact Or.inl ((J.subtype.map_isConj hz).trans hxy.symm)
  · exact Or.inr ((J.subtype.map_isConj hv).trans hxy.symm)

/-- Ambient conjugacy between involutions of the original S is already
realized by the literal join L ∨ O²(H), without identifying that join with a model. -/
theorem Preparation.triality_completion_controls_involution_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse))
    (x y : G) (hx : x∈sourceS L H) (hy : y∈sourceS L H)
    (hx2 : orderOf x=2) (hy2 : orderOf y=2) :
    IsConj x y ↔ ∃ g∈L⊔residual H, g*x*g⁻¹=y := by
  constructor
  · intro hxy
    obtain ⟨_,z,v,_,_,_,_,_,hn,hclasses⟩ := d.triality_completion_involution_classes h hH hp m hm he
    let J := L⊔residual H
    have hSJ : sourceS L H≤J :=
      (d.triality_sourceS_le_factors h hH.1.1.2 hp m hm he 1).trans le_sup_right
    let a : J := ⟨x,hSJ hx⟩
    let b : J := ⟨y,hSJ hy⟩
    have ha2 : orderOf a=2 := (orderOf_injective J.subtype Subtype.val_injective a).symm.trans hx2
    have hb2 : orderOf b=2 := (orderOf_injective J.subtype Subtype.val_injective b).symm.trans hy2
    have hab : IsConj a b := by
      rcases hclasses a hx ha2 with ha|ha <;> rcases hclasses b hy hb2 with hb|hb
      · exact ha.symm.trans hb
      · exact (hn (((J.subtype.map_isConj ha).trans hxy).trans (J.subtype.map_isConj hb).symm)).elim
      · exact (hn (((J.subtype.map_isConj hb).trans hxy.symm).trans (J.subtype.map_isConj ha).symm)).elim
      · exact ha.symm.trans hb
    obtain ⟨g,hg⟩ := isConj_iff.mp hab
    exact ⟨g.val,g.property,congrArg Subtype.val hg⟩
  · rintro ⟨g,_,hg⟩
    exact isConj_iff.mpr ⟨g,hg⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
