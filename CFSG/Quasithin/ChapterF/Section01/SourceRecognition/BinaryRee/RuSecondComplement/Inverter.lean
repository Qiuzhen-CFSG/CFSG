module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Geometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondEndpointRecognition

/-!
# Lifting the good native inverter in the original second parabolic

Faithfulness of the actual cubic-normalizer action makes a lift of the native
inverter an involution which inverts the original selected cubic. Its literal
conjugation action then gives the whole second-endpoint equivalence, preserving
all original core coordinates. The final range classification supplies the
inverter membership used here.

Source: Aschbacher–Smith F.1.12 and original J.4.5.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
open ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.F₂_equiv_of_inverter_mem_range (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (m:SecondCubicMarking (p:=p) B5)
    (hb:CubicAction.inverter∈(secondCubicNormalizerAction B5 m.X m.coordinates).range) :
    ∃E:Tits.ExceptionalParabolics.FullRee.second≃*p.F₂ B5 m.X,
      ∀a:CubicAction.A,(E (CubicAction.coreInclusion a):G)=(m.coordinates.symm a:G) := by
  let f:=secondCubicNormalizerAction B5 m.X m.coordinates
  obtain ⟨bN,hbN⟩:=hb
  let cN:secondCubicNormalizer B5 m.X:=⟨((m.generator:p.parabolic):G),m.generator_mem⟩
  have hfc:f cN=CubicAction.cubic:=m.action_generator_normalizer
  have hfb:f bN=CubicAction.inverter:=hbN
  have hbsq:bN^2=1 := by
    apply m.action_injective
    rw [map_pow,map_one,hfb]
    change (CubicAction.action Tits.AmalgamRigidity.FullRee.SecondExtension.reflection)^2=1
    rw [←map_pow,Tits.AmalgamRigidity.FullRee.SecondExtension.weyl_relations.square,map_one]
  have hbc:bN*cN*bN⁻¹=cN⁻¹ := by
    apply m.action_injective
    change f (bN*cN*bN⁻¹)=f cN⁻¹
    simp only [map_mul,map_inv,hfb,hfc]
    exact CubicAction.inverter_inverts
  let c:p.F₂ B5 m.X:=⟨(cN:G),cN.property.1⟩
  let b:p.F₂ B5 m.X:=⟨(bN:G),bN.property.1⟩
  have hc:orderOf c=3 := by
    rw [←Subgroup.orderOf_coe]
    exact m.generator_ambient_order
  have hb2:b^2=1:=Subtype.ext (congrArg (fun z:secondCubicNormalizer B5 m.X=>(z:G)) hbsq)
  have hbc':b*c*b⁻¹=c⁻¹:=Subtype.ext
    (congrArg (fun z:secondCubicNormalizer B5 m.X=>(z:G)) hbc)
  have hact:∀a:CubicAction.A,(m.coordinates.symm (CubicAction.inverter a):G)=
      (b:G)*(m.coordinates.symm a:G)*(b:G)⁻¹ := by
    intro a
    have hh:=secondCoreAction_apply B5 m.coordinates
      ⟨(bN:G),p.F₂_le_parabolic B5 m.X bN.property.1⟩ (m.coordinates.symm a)
    rw [m.coordinates.apply_symm_apply] at hh
    change (m.coordinates.symm (f bN a):G)=_ at hh
    rwa [hfb] at hh
  obtain ⟨E,hE,_,_⟩:=s.F₂_equiv_of_native_complement B5 hi m.X m.quotient m.coordinates
    c b hc hb2 hbc' m.conjugation hact
  exact ⟨E,hE⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
