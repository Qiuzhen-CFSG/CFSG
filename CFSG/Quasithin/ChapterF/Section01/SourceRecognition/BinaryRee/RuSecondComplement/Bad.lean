module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Geometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondInvolutionEscape.NoElement

/-!
# Excluding the twisted native actor from the source normalizer

The native twisted actor squares to conjugation by root seven. That root is
fixed by the cubic and therefore has an actual lift in the original normalizer.
Faithfulness gives equality of the source square with this literal lift, which
the source involution count has excluded.

Source: the binary Ree case of Aschbacher–Smith F.1.12/J.4.5.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.badActor_not_mem_range (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (m:SecondCubicMarking (p:=p) B5) :
    CubicAction.badActor∉(secondCubicNormalizerAction B5 m.X m.coordinates).range := by
  rintro ⟨v,hv⟩
  let f:=secondCubicNormalizerAction B5 m.X m.coordinates
  have hfv:f v=CubicAction.badActor:=hv
  have hz:CubicAction.cubic (CubicAction.generator 7)=CubicAction.generator 7 := by
    rw [CubicAction.cubic_generator]
    decide +kernel
  let z:CubicAction.fixedCore:=⟨CubicAction.generator 7,hz⟩
  let zN:secondCubicNormalizer B5 m.X:=⟨m.coordinates.symm z,m.native_fixed_lift_mem z⟩
  have hfz:f zN=MulAut.conj (CubicAction.generator 7) := by
    have hh:=m.action_core (m.coordinates.symm z) (m.native_fixed_lift_mem z)
    rw [m.coordinates.apply_symm_apply] at hh
    simpa only [f,zN,z] using hh
  have hv2:v^2=zN := by
    apply m.action_injective
    change f (v^2)=f zN
    rw [map_pow,hfv,hfz,CollectedBitVectors.badActor_square]
  let vF:p.F₂ B5 m.X:=⟨(v:G),v.property.1⟩
  apply s.no_twisted_F₂_element B5 hi m.X m.quotient m.coordinates vF
  · intro a
    have hh:=secondCoreAction_apply B5 m.coordinates
      ⟨(v:G),p.F₂_le_parabolic B5 m.X v.property.1⟩ a
    change (m.coordinates.symm (f v (m.coordinates a)):G)=_ at hh
    rwa [hfv] at hh
  · exact congrArg (fun x:secondCubicNormalizer B5 m.X=>(x:G)) hv2

end CFSG.Quasithin.ChapterJ.RuSubgroup
