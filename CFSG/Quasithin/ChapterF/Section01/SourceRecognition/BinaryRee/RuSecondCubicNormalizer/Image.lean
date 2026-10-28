module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Geometry

/-!
# The original second cubic normalizer image

The literal conjugation homomorphism maps the original normalizer into
the native cubic normalizer. Its image contains the fixed inner group and
the cubic, with explicit preimages in the unchanged source subgroups.

Source: Aschbacher–Smith J.4.4–5 and F.1.12.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
open Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}
    {B5:Sylow 5 d.toTypeRuSetup.H} (m:SecondCubicMarking (p:=p) B5)

 theorem image_le_normalizer : (secondCubicNormalizerAction B5 m.X m.coordinates).range≤
    normalizer (zpowers CubicAction.cubic:Set (MulAut firstParabolicCore)) := by
  let f:=secondCoreAction B5 m.coordinates
  have hX:(m.X:Subgroup p.parabolic)=zpowers (m.generator:p.parabolic):=by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr m.generator.property)
    rw [p.card_sylow_three m.X,Nat.card_zpowers,orderOf_coe,m.generator_order]
  have hmap:(m.X:Subgroup p.parabolic).map f=zpowers CubicAction.cubic:=by
    rw [hX,f.map_zpowers,m.action_generator]
  have hsub:(p.cubicSubgroup m.X).subgroupOf p.parabolic=(m.X:Subgroup p.parabolic):=by
    exact comap_map_eq_self_of_injective p.parabolic.subtype_injective _
  rintro a ⟨z,rfl⟩
  let zP:p.parabolic:=⟨z,(p.F₂_le_parabolic B5 m.X) z.property.1⟩
  have hz:zP∈normalizer ((m.X:Subgroup p.parabolic):Set p.parabolic):=by
    have hP:p.cubicSubgroup m.X≤p.parabolic:=map_subtype_le _
    rw [←hsub,←subgroupOf_normalizer_eq hP]
    exact z.property.2
  have hh: f zP∈normalizer ((m.X:Subgroup p.parabolic).map f:Set (MulAut firstParabolicCore)) :=
    (le_normalizer_map f) ⟨zP,hz,rfl⟩
  rw [hmap] at hh
  exact hh

 theorem innerCore_le_image : CubicAction.cubicInnerCore≤
    (secondCubicNormalizerAction B5 m.X m.coordinates).range := by
  apply sup_le
  · rintro α ⟨a,ha,rfl⟩
    let af:CubicAction.fixedCore:=⟨a,ha⟩
    refine ⟨⟨m.coordinates.symm a,m.native_fixed_lift_mem af⟩,?_⟩
    rw [m.action_core,m.coordinates.apply_symm_apply]
  · apply zpowers_le.mpr
    exact ⟨⟨((m.generator:p.parabolic):G),m.generator_mem⟩,m.action_generator_normalizer⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
