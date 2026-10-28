module
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuAmalgam.Marking
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee

/-!
# The marked faithful completion in the original generated source subgroup

The genuine endpoint recognition and simultaneous marking adjustment construct
both local equivalences. Completing their inclusion amalgam in the literal
join F=F₁∨F₂ preserves every source inclusion, the original central involution
and the selected five-subgroup. The Type-Ru consumer selects all original data
internally; no compatible-amalgam or local-recognition premise is retained.

This is the original completion used by the J.4.7 smallness argument.
Source: Aschbacher–Smith J.4.5–7, printed pp.441–445.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices FiveHexagon.MarkedInverter
open Theory.GroupTheory RankTwoAmalgam
open Tits.ExceptionalParabolics.FullRee
open ChapterF.SourceCompletion.BinaryRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The source inclusion amalgam is completed inside the same generated F. -/
def sourceCompletionOfIso (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (i:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam) : Completion (p.F B5 X) :=
  (FaithfulCompletion.ofGeneratedSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
    (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)).comapIso i.symm

theorem sourceCompletionOfIso_left (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (i:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam) (a:first) :
    ((sourceCompletionOfIso B5 X i).left a:G)=(i.left.symm a:G) := by
  exact FaithfulCompletion.ofGeneratedSubgroups_left _ _ _ _ _ (i.left.symm a)

theorem sourceCompletionOfIso_right (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (i:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam) (a:second) :
    ((sourceCompletionOfIso B5 X i).right a:G)=(i.right.symm a:G) := by
  exact FaithfulCompletion.ofGeneratedSubgroups_right _ _ _ _ _ (i.right.symm a)

theorem sourceCompletionOfIso_ranges (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (i:Iso (ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
      (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)) amalgam) :
    (sourceCompletionOfIso B5 X i).left.range=(p.F₁ B5).subgroupOf (p.F B5 X) ∧
    (sourceCompletionOfIso B5 X i).right.range=(p.F₂ B5 X).subgroupOf (p.F B5 X) := by
  let q₀:=FaithfulCompletion.ofGeneratedSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
    (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X)
  exact ⟨(FaithfulCompletion.comapIso_left_range q₀ i.symm).trans
      (FaithfulCompletion.ofGeneratedSubgroups_left_range _ _ _ _ _),
    (FaithfulCompletion.comapIso_right_range q₀ i.symm).trans
      (FaithfulCompletion.ofGeneratedSubgroups_right_range _ _ _ _ _)⟩

theorem SourceChoice.exists_marked_completion (s:SourceChoice p) (c:Centralizers.Choices d)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    ∃(q:Completion (p.F B5 X))(e:first≃*p.F₁ B5)(e₂:second≃*p.F₂ B5 X),
      (∀a:first,(q.left a:G)=(e a:G)) ∧
      (∀a:second,(q.right a:G)=(e₂ a:G)) ∧
      (e modelZ:G)=c.z ∧
      (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5 ∧
      q.left.range=(p.F₁ B5).subgroupOf (p.F B5 X) ∧
      q.right.range=(p.F₂ B5 X).subgroupOf (p.F B5 X) := by
  obtain ⟨i,hz,hfive⟩:=s.marked_fullRee_iso c B5 hi X hm
  exact ⟨sourceCompletionOfIso B5 X i,i.left.symm,i.right.symm,
    sourceCompletionOfIso_left B5 X i,sourceCompletionOfIso_right B5 X i,
    hz,hfive,sourceCompletionOfIso_ranges B5 X i⟩

/-- Original Type-Ru data supplies a faithfully and literally marked completion. -/
theorem marked_completion_of_typeRu (h:IsTypeRu G) :
    ∃(d:LocalSetup G)(p:Plane d)(s:SourceChoice p)(c:Centralizers.Choices d)
      (B5:Sylow 5 d.toTypeRuSetup.H)(X:Sylow 3 p.parabolic)
      (q:Completion (p.F B5 X))(e:first≃*p.F₁ B5)(e₂:second≃*p.F₂ B5 X),
      (∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) ∧
      Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)) ∧
      (∀a:first,(q.left a:G)=(e a:G)) ∧
      (∀a:second,(q.right a:G)=(e₂ a:G)) ∧
      (e modelZ:G)=c.z ∧
      (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5 ∧
      q.left.range=(p.F₁ B5).subgroupOf (p.F B5 X) ∧
      q.right.range=(p.F₂ B5 X).subgroupOf (p.F B5 X) := by
  obtain ⟨d,p,⟨s⟩⟩:=source_J4_choice h
  obtain ⟨c⟩:=SourceCompletion.exists_choices d
  obtain ⟨B5,hi⟩:=s.inverts_sylow_five
  obtain ⟨X,_,hm,_⟩:=s.exists_secondParabolic p B5 hi
  obtain ⟨q,e,e₂,hl,hr,hz,hfive,hranges⟩:=s.exists_marked_completion c B5 hi X hm
  exact ⟨d,p,s,c,B5,X,q,e,e₂,hi,hm,hl,hr,hz,hfive,hranges⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
