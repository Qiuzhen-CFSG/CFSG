module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuAmalgam
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuAmalgam.Marking.Five

/-!
# The source amalgam with its original five and central involution

Start with the proved whole compatible amalgam isomorphism. Conjugation by
one element of the common source subgroup adjusts all three maps, retaining
both commuting squares and the same p, B₅ and X. The first map then sends
the model rotation subgroup to the original B₅ and modelZ to the chosen z.
This supplies the marked-completion input to the original J.4 geometry.

Source: Aschbacher–Smith J.4.7–8, using the genuine F.1.12 recognition.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices FiveHexagon.MarkedInverter
open Theory.GroupTheory RankTwoAmalgam
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 def sourceConjugationIso (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (t:p.T_F B5) :
    Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X))
    (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) where
  toParabolicEquiv:=⟨MulAut.conj ⟨t,p.T_F_le_F₁ B5 t.property⟩,
    MulAut.conj t,MulAut.conj ⟨t,p.T_F_le_F₂ B5 X t.property⟩⟩
  left_commutes _:=rfl
  right_commutes _:=rfl

 theorem SourceChoice.adjust_fullRee_iso (s:SourceChoice p) (c:Centralizers.Choices d)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (i:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam) :
    ∃j:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam,
      (j.left.symm modelZ:G)=c.z ∧
      (zpowers modelRotation).map ((p.F₁ B5).subtype.comp j.left.symm.toMonoidHom)=B5Image B5 := by
  obtain ⟨t,ht⟩:=s.exists_first_marking_adjustment B5 hi i.left.symm
  let j:=i.symm.trans (sourceConjugationIso B5 X t)
  refine ⟨j.symm,first_equiv_marks_z c B5 j.left,?_⟩
  exact ht

 theorem SourceChoice.marked_fullRee_iso (s:SourceChoice p) (c:Centralizers.Choices d)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    ∃j:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam,
      (j.left.symm modelZ:G)=c.z ∧
      (zpowers modelRotation).map ((p.F₁ B5).subtype.comp j.left.symm.toMonoidHom)=B5Image B5 := by
  obtain ⟨i⟩:=s.compatible_fullRee_iso B5 hi X hm
  exact s.adjust_fullRee_iso c B5 hi X i
end CFSG.Quasithin.ChapterJ.RuSubgroup
