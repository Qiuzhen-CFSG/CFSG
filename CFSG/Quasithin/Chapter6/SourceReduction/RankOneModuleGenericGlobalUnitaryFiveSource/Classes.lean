module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.Classes
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.NativeInvolutions

/-!
# Exact two-class fusion on the original U₅(4) plane-core center

The reduced endpoint comparison identifies the original plane-core center
with the native one. Its two Hermitian types are exhaustive and remain
separate under the whole extension. Ambient Burnside fusion control moves
any conjugator between original central elements into the full normalizer;
the published endpoint marking then reduces it to native endpoint fusion.
Thus ambient, native, extension and reduced-endpoint fusion all agree on
this actual center. The same two marked representatives cover all native
involutions inside this identical extension.

The hypotheses retain both orientations, the whole residual and the original
KnownSimple input. The impossible unreversed orientation is discharged by
the prepared-source theorem. All endpoint, whole-D and range equations use
the same marking. This is the central part of F.4.35, not ambient involution
coverage: outer transfer and the full F.4.42 equality remain to be proved.
Source: Aschbacher–Smith F.4.35, printed p.292.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_center_image_iff {X : Type*} [Group X]
    {L P : Subgroup G} {R Q : Subgroup X} (hLP : L ≤ P) (e : P ≃* Q)
    (hR : (L.subgroupOf P).map (Q.subtype.comp e.toMonoidHom) = R) (y : P) :
    y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ↔
      (e y).val ∈ (center (R.pCoreIn 2)).map (R.pCoreIn 2).subtype := by
  let f := Q.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hQ : ((L.pCoreIn 2).subgroupOf P).map f = R.pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 L P hLP,map_pCoreIn_of_injective 2 _ f hf,hR]
  have hQP : L.pCoreIn 2 ≤ P := (L.pCoreIn_le 2).trans hLP
  let eq : L.pCoreIn 2 ≃* R.pCoreIn 2 :=
    (subgroupOfEquivOfLe hQP).symm.trans
      ((((L.pCoreIn 2).subgroupOf P).equivMapOfInjective f hf).trans
        (MulEquiv.subgroupCongr hQ))
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨eq v,(centerCongr eq ⟨v,hv⟩).property,?_⟩
    change f ⟨v,hQP v.property⟩ = (e y).val
    exact congrArg f (Subtype.ext he)
  · rintro ⟨v,hv,he⟩
    let z := eq.symm v
    have hz : z ∈ center (L.pCoreIn 2) := (centerCongr eq.symm ⟨v,hv⟩).property
    have heq : f ⟨z.val,hQP z.property⟩ = (e y).val :=
      (congrArg Subtype.val (eq.apply_symm_apply v)).trans he
    have hzy : (⟨z.val,hQP z.property⟩ : P) = y := hf heq
    exact ⟨z,hz,congrArg Subtype.val hzy⟩

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Exact two-class coverage of the original plane-core center and fusion
comparison in the native carrier and the same full extension. -/
theorem Preparation.unitaryFive_marked_center_classes
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
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le t))) (r.extension.baseHom u)) := by
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · exfalso
    apply d.not_unitaryFive_unreversed h hH.1.1.2 hp U
    rw [hs]
    exact ⟨a.comparison⟩
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  have hR : (L.subgroupOf P).map (U.rightParabolic.subtype.comp a.comparison.left.toMonoidHom) =
      U.rightLocalImage := by
    have hres : L.subgroupOf P = solvableResidual P := by
      have he : (solvableResidual P).map P.subtype = L :=
        d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
      rw [←he]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [hres,←map_map,map_solvableResidual_eq a.comparison.left.toMonoidHom
      a.comparison.left.surjective]
    rfl
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  have hcoord (x : P) := core_center_image_iff hLP a.comparison.left hR x
  have hmark (x : P) :
      inclusion r.extension.right_le (F.left (inclusion r.left_le x)) =
        r.extension.baseHom (a.comparison.left x).val := Subtype.ext (h0 x)
  have hequiv (x y : P) : IsConj x y ↔ IsConj (a.comparison.left x) (a.comparison.left y) := by
    constructor
    · exact a.comparison.left.toMonoidHom.map_isConj
    · intro hh
      have he := a.comparison.left.symm.toMonoidHom.map_isConj hh
      change IsConj (a.comparison.left.symm (a.comparison.left x))
        (a.comparison.left.symm (a.comparison.left y)) at he
      simpa only [a.comparison.left.symm_apply_apply] using he
  have hfus (x y : P) (hx : x.val ∈ Z) (hy : y.val ∈ Z) :
      IsConj x.val y.val ↔ IsConj x y := by
    constructor
    · intro hh
      have hlocal := (d.unitaryFive_plane_center_local_fusion h hH hp U hc
        (inclusion r.left_le x) (inclusion r.left_le y) hx hy).mp hh
      have he := (inclusion r.extension.right_le).map_isConj (F.left.toMonoidHom.map_isConj hlocal)
      change IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le x)))
        (inclusion r.extension.right_le (F.left (inclusion r.left_le y))) at he
      rw [hmark,hmark] at he
      exact (hequiv x y).mpr ((FiveExtension.right_core_center_fusion U r.extension _ _
        ((hcoord x).mp hx) ((hcoord y).mp hy)).mp he)
    · exact P.subtype.map_isConj
  let z : P := a.comparison.left.symm U.longInvolution
  let t : P := a.comparison.left.symm U.shortInvolution
  have hz : z.val ∈ Z := (hcoord z).mpr (by
    simpa only [z,a.comparison.left.apply_symm_apply] using U.longInvolution_mem_center)
  have ht : t.val ∈ Z := (hcoord t).mpr (by
    simpa only [t,a.comparison.left.apply_symm_apply] using U.shortInvolution_mem_center)
  have hord (y : U.rightParabolic) : orderOf (a.comparison.left.symm y).val = orderOf y := by
    rw [Subgroup.orderOf_coe,a.comparison.left.symm.orderOf_eq]
  refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,hz,ht,
    (hord _).trans U.longInvolution_order,(hord _).trans U.shortInvolution_order,?_,?_,?_,?_⟩
  · intro he
    have hh := U.rightParabolic.subtype.map_isConj ((hequiv z t).mp ((hfus z t hz ht).mp he))
    change IsConj (a.comparison.left z).val (a.comparison.left t).val at hh
    rw [a.comparison.left.apply_symm_apply,a.comparison.left.apply_symm_apply] at hh
    exact U.long_short_not_isConj hh
  · intro x hx hx1
    have hxn : a.comparison.left x ≠ 1 := by
      intro he
      exact hx1 (a.comparison.left.injective (he.trans a.comparison.left.map_one.symm))
    rcases U.right_core_center_two_classes _ ((hcoord x).mp hx) hxn with he | he
    · apply Or.inl
      apply (hequiv z x).mpr
      exact (a.comparison.left.apply_symm_apply U.longInvolution).symm ▸ he
    · apply Or.inr
      apply (hequiv t x).mpr
      exact (a.comparison.left.apply_symm_apply U.shortInvolution).symm ▸ he
  · intro x y hx hy
    refine ⟨(hfus x y hx hy).trans ((hequiv x y).trans
      (U.right_core_center_fusion _ _ ((hcoord x).mp hx) ((hcoord y).mp hy)).symm),?_,hfus x y hx hy⟩
    rw [hmark,hmark]
    exact (hfus x y hx hy).trans ((hequiv x y).trans
      (FiveExtension.right_core_center_fusion U r.extension _ _
        ((hcoord x).mp hx) ((hcoord y).mp hy)).symm)
  · intro u hu
    rw [hmark,hmark]
    simp only [a.comparison.left.apply_symm_apply]
    exact (U.involution_two_classes u hu).elim
      (fun hh => Or.inl (r.extension.baseHom.map_isConj hh))
      (fun hh => Or.inr (r.extension.baseHom.map_isConj hh))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
