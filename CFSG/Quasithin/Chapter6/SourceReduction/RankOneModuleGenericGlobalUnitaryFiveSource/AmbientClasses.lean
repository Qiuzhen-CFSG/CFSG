module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Classes
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FixedFusion

/-!
# Exactly two ambient involution classes on the U₅(4) marking

Cyclic field transfer first puts an ambient involution into the original S.
The endpoint equation identifies its marked image with a native involution.
Native coverage moves that image to the plane-core center; connected fixed
paths transport the conjugacy through the same inverse full-endpoint maps.
Thus every ambient involution is fused into the original plane-core center.
The proved center nonfusion now gives exactly two ambient classes, represented
by the inverse images of the native long and short involutions.

Both admitted orientations and the whole residual are retained. The final
marked theorem keeps every endpoint, whole-D and range equation, along with
native coverage and center fusion. It asserts neither S=T nor the F.4.42
full ambient short centralizer equality or the F.4.43 ambient order.
Source: Aschbacher–Smith F.4.30,35,38, pp.290–294 (`refs/quasithin.pdf`).
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Every original ambient involution is conjugate into the actual plane-core
center, using the identical published extension and endpoint marking. -/
theorem Preparation.unitaryFive_involution_fused_into_plane_center
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (x : G) (hx : orderOf x = 2) :
    ∃ z ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype, IsConj x z := by
  obtain ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,hcov,_⟩ :=
    d.unitaryFive_marked_native_involutions h hH hp U hc r
  obtain ⟨y,hy,hxy⟩ := d.unitaryFive_involution_fused_into_sourceS h hH hp U hc x hx
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  have hyr : y ∈ (T : Subgroup G) ⊓ L := hs ▸ hy
  let p : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 :=
    ⟨y,(show (T : Subgroup G) ⊓ L ≤ _ from le_sup_right.trans le_sup_left) hyr⟩
  let q : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 :=
    ⟨y,(show (T : Subgroup G) ⊓ L ≤ _ from le_sup_right.trans le_sup_left) hyr⟩
  let yd : (normalizerAmalgam L (residual H)).M₁₂ :=
    ⟨y,r.left_le p.property,r.right_le q.property⟩
  have hy2 : orderOf y = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hu : orderOf (a.comparison.left p).val = 2 := by
    rw [Subgroup.orderOf_coe,a.comparison.left.orderOf_eq,←Subgroup.orderOf_coe]
    exact hy2
  obtain ⟨z,hz,_,huz⟩ := hcov (a.comparison.left p).val hu
  let l := (normalizer (residual H : Set G)).subtype.comp F.right.symm.toMonoidHom
  let b := (normalizer (L : Set G)).subtype.comp F.left.symm.toMonoidHom
  have hcompat (v : r.extension.middle) :
      l (inclusion inf_le_left v) = b (inclusion inf_le_right v) := by
    have h₁ := congrArg Subtype.val (F.symm.right_commutes v)
    have h₀ := congrArg Subtype.val (F.symm.left_commutes v)
    exact h₁.trans h₀.symm
  have he : inclusion (inf_le_left.trans r.extension.left_le) (F.middle yd) =
      r.extension.baseHom (a.comparison.left p).val := by
    apply Subtype.ext
    exact (congrArg Subtype.val (F.left_commutes yd)).symm.trans (h0 p)
  have ht := r.extension.right_fusion_of_middle U l b hcompat (F.middle yd)
    (F.left (inclusion r.left_le z)) (he.symm ▸ huz)
  change IsConj (F.left.symm (inclusion inf_le_right (F.middle yd))).val
    (F.left.symm (F.left (inclusion r.left_le z))).val at ht
  have heleft : inclusion inf_le_right (F.middle yd) = F.left (inclusion r.left_le p) :=
    (F.left_commutes yd).symm
  rw [heleft] at ht
  have hpback : (F.left.symm (F.left (inclusion r.left_le p))).val = y :=
    congrArg Subtype.val (F.left.symm_apply_apply (inclusion r.left_le p))
  have hzback : (F.left.symm (F.left (inclusion r.left_le z))).val = z.val :=
    congrArg Subtype.val (F.left.symm_apply_apply (inclusion r.left_le z))
  have ht' : IsConj y z.val := (congrArg₂ IsConj hpback hzback) ▸ ht
  exact ⟨z.val,hz,hxy.trans ht'⟩

/-- The same marked long and short representatives exhaust all ambient
involutions and remain distinct. All earlier marking and native-fusion
conclusions are retained on the same maps and extension. -/
theorem Preparation.unitaryFive_marked_ambient_classes
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
      let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
      let z : P := a.comparison.left.symm U.longInvolution
      let t : P := a.comparison.left.symm U.shortInvolution
      z.val ∈ Z ∧ t.val ∈ Z ∧ orderOf z.val = 2 ∧ orderOf t.val = 2 ∧
      ¬ IsConj z.val t.val ∧
      (∀ x : P, x.val ∈ Z → x ≠ 1 → IsConj z x ∨ IsConj t x) ∧
      (∀ x y : P, x.val ∈ Z → y.val ∈ Z →
        (IsConj x.val y.val ↔ IsConj (a.comparison.left x).val (a.comparison.left y).val) ∧
        (IsConj x.val y.val ↔ IsConj
          (inclusion r.extension.right_le (F.left (inclusion r.left_le x)))
          (inclusion r.extension.right_le (F.left (inclusion r.left_le y)))) ∧
        (IsConj x.val y.val ↔ IsConj x y)) ∧
      (∀ u : U.Carrier, orderOf u = 2 →
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le z))) (r.extension.baseHom u) ∨
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le t))) (r.extension.baseHom u)) ∧
      (∀ x : G, orderOf x = 2 → IsConj z.val x ∨ IsConj t.val x) := by
  obtain ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,hz,ht,hzo,hto,hne,hcov,hfus,hnative⟩ :=
    d.unitaryFive_marked_center_classes h hH hp U hc r
  refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,hz,ht,hzo,hto,hne,hcov,hfus,hnative,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := d.unitaryFive_involution_fused_into_plane_center h hH hp U hc r x hx
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  have hyP : y ∈ P := hLP ((pCoreIn_le 2 L) (map_subtype_le _ hy))
  let v : P := ⟨y,hyP⟩
  have hv1 : v ≠ 1 := by
    intro he
    have hy1 : y = 1 := congrArg Subtype.val he
    have hx1 : x = 1 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hxy
      apply (MulAut.conj g).injective
      simpa only [MulAut.conj_apply, mul_one, mul_inv_cancel] using hg.trans hy1
    rw [hx1,orderOf_one] at hx
    omega
  exact (hcov v hy hv1).elim
    (fun hh => Or.inl ((P.subtype.map_isConj hh).trans hxy.symm))
    (fun hh => Or.inr ((P.subtype.map_isConj hh).trans hxy.symm))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
