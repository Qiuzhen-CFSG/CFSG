module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OddOuter
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FixedFusion
-- Internal proof split: reuse the core-center transport of this source family.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Classes

/-!
# Whole-endpoint involution fusion for the original U₅(4) row

The same full-normalizer marking preserves conjugacy to each plane-core
central involution on both entire endpoints. The proof moves an endpoint
involution into the original Sylow, uses S=T and fixed-path fusion to move
it into the plane-core center simultaneously in the original group and
extension, and applies the Hermitian center fusion comparison there.

Source: Aschbacher–Smith F.4.35,38,42–43, printed pp.292,294–296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
namespace UnitaryFiveFusion
@[expose] def markedLeftHom
    {L K R : Subgroup G} {U : Model 4}
    (r : UnitaryFiveNormalizerMarking L K R U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L K) r.extension.amalgam.reverse) :
    normalizer (L : Set G) →* r.extension.carrier :=
  (inclusion r.extension.right_le).comp F.left.toMonoidHom

@[expose] def markedRightHom
    {L K R : Subgroup G} {U : Model 4}
    (r : UnitaryFiveNormalizerMarking L K R U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L K) r.extension.amalgam.reverse) :
    normalizer (K : Set G) →* r.extension.carrier :=
  (inclusion r.extension.left_le).comp F.right.toMonoidHom

variable
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
include d h hH hp hc h0

omit h0 in
private theorem center_image (y : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0) :
    y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ↔
      (a.comparison.left y).val ∈ (center (U.rightLocalImage.pCoreIn 2)).map
        (U.rightLocalImage.pCoreIn 2).subtype := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  apply core_center_image_iff hLP a.comparison.left
  have hres : L.subgroupOf P = solvableResidual P := by
    have he : (solvableResidual P).map P.subtype = L :=
      d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
    rw [←he]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  rw [hres,←map_map,map_solvableResidual_eq a.comparison.left.toMonoidHom
    a.comparison.left.surjective]
  rfl

private theorem center_fusion
    (x y : normalizer (L : Set G))
    (hx : x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hy : y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :
    IsConj x.val y.val ↔ IsConj (markedLeftHom r F x) (markedLeftHom r F y) := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hZP : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ≤ P :=
    (map_subtype_le _).trans ((pCoreIn_le 2 L).trans (le_sup_left.trans le_sup_left))
  let xP : P := ⟨x.val,hZP hx⟩
  let yP : P := ⟨y.val,hZP hy⟩
  have hm (v : P) : markedLeftHom r F (inclusion r.left_le v) =
      r.extension.baseHom (a.comparison.left v).val := Subtype.ext (h0 v)
  constructor
  · intro hh
    exact (markedLeftHom r F).map_isConj
      ((d.unitaryFive_plane_center_local_fusion h hH hp U hc x y hx hy).mp hh)
  · intro hh
    change IsConj (markedLeftHom r F (inclusion r.left_le xP))
      (markedLeftHom r F (inclusion r.left_le yP)) at hh
    rw [hm,hm] at hh
    have hc' := (FiveExtension.right_core_center_fusion U r.extension _ _
      ((center_image d h hH hp U hc a xP).mp hx)
      ((center_image d h hH hp U hc a yP).mp hy)).mp hh
    have hg := a.comparison.left.symm.toMonoidHom.map_isConj hc'
    simp only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] at hg
    exact P.subtype.map_isConj hg

private theorem sylow_placement (v : normalizer (L : Set G))
    (hv : v.val ∈ (T : Subgroup G)) (hv2 : orderOf v.val=2) :
    ∃ y : normalizer (L : Set G), y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
      IsConj v.val y.val ∧ IsConj (markedLeftHom r F v) (markedLeftHom r F y) := by
  let B := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hvS : v.val ∈ sourceS L H := (d.unitaryFive_sourceS_eq_sylow h hH hp U hc r).ge hv
  have hvTL : v.val ∈ (T : Subgroup G) ⊓ L :=
    (d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc).le hvS
  let vB : B := ⟨v.val,(show (T : Subgroup G) ⊓ L ≤ B from le_sup_right.trans le_sup_left) hvTL⟩
  let vD : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) :=
    ⟨v.val,v.property,(hH.1.1.2.trans (le_normalizer_residual H)) hv⟩
  have hord : orderOf (a.comparison.left vB).val=2 := by
    rw [Subgroup.orderOf_coe,a.comparison.left.orderOf_eq,←Subgroup.orderOf_coe]
    exact hv2
  obtain ⟨y,hy,_,hvy⟩ := U.involution_to_right_core_center (a.comparison.left vB).val hord
  let yB := a.comparison.left.symm y
  have hyG : yB.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype :=
    (center_image d h hH hp U hc a yB).mpr (by
      simpa only [yB,a.comparison.left.apply_symm_apply] using hy)
  have hm (x : B) : markedLeftHom r F (inclusion r.left_le x)=
      r.extension.baseHom (a.comparison.left x).val := Subtype.ext (h0 x)
  have hvyE : IsConj (markedLeftHom r F v) (markedLeftHom r F (inclusion r.left_le yB)) := by
    change IsConj (markedLeftHom r F (inclusion r.left_le vB)) _
    rw [hm,hm,a.comparison.left.apply_symm_apply]
    exact r.extension.baseHom.map_isConj hvy
  let l := (normalizer (residual H : Set G)).subtype.comp F.right.symm.toMonoidHom
  let b := (normalizer (L : Set G)).subtype.comp F.left.symm.toMonoidHom
  have hcompat (x : r.extension.middle) :
      l (inclusion inf_le_left x)=b (inclusion inf_le_right x) :=
    (congrArg Subtype.val (F.symm.right_commutes x)).trans
      (congrArg Subtype.val (F.symm.left_commutes x)).symm
  have hmD : inclusion (inf_le_left.trans r.extension.left_le) (F.middle vD) =
      markedLeftHom r F v := Subtype.ext (congrArg Subtype.val (F.left_commutes vD)).symm
  have hxy := r.extension.right_fusion_of_middle U l b hcompat (F.middle vD)
    (F.left (inclusion r.left_le yB)) (hmD.symm ▸ hvyE)
  have hleft : inclusion inf_le_right (F.middle vD) = F.left v := (F.left_commutes vD).symm
  change IsConj (F.left.symm (inclusion inf_le_right (F.middle vD))).val
    (F.left.symm (F.left (inclusion r.left_le yB))).val at hxy
  rw [hleft] at hxy
  have hvback : (F.left.symm (F.left v)).val=v.val :=
    congrArg Subtype.val (F.left.symm_apply_apply v)
  have hyback : (F.left.symm (F.left (inclusion r.left_le yB))).val=yB.val :=
    congrArg Subtype.val (F.left.symm_apply_apply (inclusion r.left_le yB))
  exact ⟨inclusion r.left_le yB,hyG,(congrArg₂ IsConj hvback hyback) ▸ hxy,hvyE⟩

omit [Finite G] d h hH hp hc h0 in
private theorem conjugate_order {X : Type*} [Group X] {x y : X} (hxy : IsConj x y) :
    orderOf y = orderOf x := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  rw [←hg]
  exact (MulAut.conj g).orderOf_eq x

/-- Both ambient class predicates agree on the entire original plane normalizer. -/
theorem marked_left_class
    (z : normalizer (L : Set G))
    (hz : z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hz2 : orderOf z.val=2) (x : normalizer (L : Set G)) :
    IsConj z.val x.val ↔ IsConj (markedLeftHom r F z) (markedLeftHom r F x) := by
  let j := markedLeftHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  by_cases hx : orderOf x.val=2
  · let P := T.subtype h.sylow_normalizes
    obtain ⟨v,hxv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
      (by simpa only [Subgroup.orderOf_coe,pow_one] using hx)
    have hvo : orderOf v.val.val=2 := (Subgroup.orderOf_coe v.val).trans
      ((conjugate_order hxv).trans ((Subgroup.orderOf_coe x).symm.trans hx))
    obtain ⟨y,hy,hvy,hvyE⟩ := sylow_placement d h hH hp U hc r a F h0 v.val v.property hvo
    have hxy := ((normalizer (L : Set G)).subtype.map_isConj hxv).trans hvy
    have hxyE := (j.map_isConj hxv).trans hvyE
    have he := center_fusion d h hH hp U hc r a F h0 z y hz hy
    exact ⟨fun hh => (he.mp (hh.trans hxy)).trans hxyE.symm,
      fun hh => (he.mpr (hh.trans hxyE)).trans hxy.symm⟩
  · constructor
    · intro hh
      exact (hx ((conjugate_order hh).trans hz2)).elim
    · intro hh
      have he := conjugate_order hh
      rw [orderOf_injective j hj,orderOf_injective j hj,
        ←Subgroup.orderOf_coe x,←Subgroup.orderOf_coe z] at he
      exact (hx (he.trans hz2)).elim

omit [Finite G] d h hH hp hc h0 in
theorem marked_overlap (x : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G)) :
    markedLeftHom r F (inclusion inf_le_left x) =
      markedRightHom r F (inclusion inf_le_right x) := by
  apply Subtype.ext
  exact (congrArg Subtype.val (F.left_commutes x)).trans
    (congrArg Subtype.val (F.right_commutes x)).symm

/-- The line endpoint preserves the same two ambient class predicates. -/
theorem marked_right_class
    (z : normalizer (L : Set G))
    (hz : z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hz2 : orderOf z.val=2) (x : normalizer (residual H : Set G)) :
    IsConj z.val x.val ↔ IsConj (markedLeftHom r F z) (markedRightHom r F x) := by
  let N := normalizer (residual H : Set G)
  let k := markedRightHom r F
  have hk : Function.Injective k := (inclusion_injective r.extension.left_le).comp F.right.injective
  by_cases hx : orderOf x.val=2
  · let P := T.subtype (hH.1.1.2.trans (le_normalizer_residual H))
    obtain ⟨v,hxv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
      (by simpa only [Subgroup.orderOf_coe,pow_one] using hx)
    let vD : (normalizer (L : Set G) ⊓ N : Subgroup G) :=
      ⟨v.val.val,h.sylow_normalizes v.property,v.val.property⟩
    let vL := inclusion inf_le_left vD
    have hxy : IsConj x.val vL.val := N.subtype.map_isConj hxv
    have hxyE : IsConj (k x) (markedLeftHom r F vL) := by
      rw [marked_overlap U r F vD]
      exact k.map_isConj hxv
    have he := marked_left_class d h hH hp U hc r a F h0 z hz hz2 vL
    exact ⟨fun hh => (he.mp (hh.trans hxy)).trans hxyE.symm,
      fun hh => (he.mpr (hh.trans hxyE)).trans hxy.symm⟩
  · have hj : Function.Injective (markedLeftHom r F) :=
      (inclusion_injective r.extension.right_le).comp F.left.injective
    constructor
    · intro hh
      exact (hx ((conjugate_order hh).trans hz2)).elim
    · intro hh
      have he := conjugate_order hh
      rw [orderOf_injective k hk,orderOf_injective (markedLeftHom r F) hj,
        ←Subgroup.orderOf_coe x,←Subgroup.orderOf_coe z] at he
      exact (hx (he.trans hz2)).elim

end UnitaryFiveFusion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
