module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondComplement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFirstEndpoint
public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.Local
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee

/-!
# The actual Type-Ru binary Ree inclusion amalgam

Both unchanged source endpoints have now been recognized. The original common
Sylow subgroup supplies the overlap equivalence. Full-Ree twist rigidity makes
these three equivalences compatible, with one and the same middle map in both
inclusion squares. All F.1.1 local inputs are constructed for this exact selected
X. The Type-Ru application chooses the original source data internally.

This is the binary Ree local recognition needed in Aschbacher–Smith J.4.5,
via F.1.12. Further normalization of the marked five-subgroup is independent
of the compatible inclusion-amalgam identification proved here.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices Theory.GroupTheory RankTwoAmalgam
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.localData_of_second_quotient (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    ChapterF.Source.BinaryRee.LocalData (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X) := by
  refine {
    le_left:=p.T_F_le_F₁ B5
    le_right:=p.T_F_le_F₂ B5 X
    sylow_left:=s.T_F_sylow_F₁ p B5 hi
    sylow_right:=s.T_F_sylow_F₂ p B5 hi X hm
    normalizer_left:=s.T_F_selfNormalizing_F₁ p B5 hi
    normalizer_right:=s.T_F_normalizer_F₂ p B5 hi X hm
    quotient_left:=s.F₁_quotient p B5 hi
    quotient_right:=p.F₂_core_quotient B5 X hm
    characteristic_left:=s.F₁_characteristic_two p B5 hi
    characteristic_right:=p.F₂_characteristic_two B5 X hm
    core_free:=?_
    card_overlap:=s.card_T_F p B5 hi }
  exact s.joined_core_eq_bot B5 (p.F₁ B5) (p.F₂ B5 X) le_sup_right
    (le_sup_right.trans le_sup_left)
    ((p.S₂_le_A B5).trans (le_sup_left.trans le_sup_left)) (s.F₂_sup_S p B5 hi X)
    (s.F₁_twoCore_le_Q p B5 hi)

theorem SourceChoice.compatible_fullRee_iso (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
        (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X))
      Tits.ExceptionalParabolics.FullRee.amalgam) := by
  obtain ⟨e₁⟩:=s.F₁_equiv_fullRee_first B5 hi
  obtain ⟨e₂⟩:=s.F₂_equiv_fullRee_second B5 hi X hm
  obtain ⟨eT⟩:=s.T_F_equiv_sylowModel B5 hi
  apply Tits.AmalgamRigidity.FullRee.iso_of_parabolicEquiv
  · refine {
      left_injective := inclusion_injective (p.T_F_le_F₁ B5)
      right_injective := inclusion_injective (p.T_F_le_F₂ B5 X)
      left_sylow := ?_
      right_sylow := ?_ }
    · obtain ⟨P,hP⟩:=s.T_F_sylow_F₁ p B5 hi
      exact ⟨P,hP.trans (inclusion_range (p.T_F_le_F₁ B5)).symm⟩
    · obtain ⟨P,hP⟩:=s.T_F_sylow_F₂ p B5 hi X hm
      exact ⟨P,hP.trans (inclusion_range (p.T_F_le_F₂ B5 X)).symm⟩
  · exact ⟨e₁,eT.trans Tits.AmalgamRigidity.FullRee.borelEquiv,e₂⟩

theorem SourceChoice.exists_compatible_fullRee_iso (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃X:Sylow 3 p.parabolic,
      Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)) ∧
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
          (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X))
        Tits.ExceptionalParabolics.FullRee.amalgam) := by
  obtain ⟨X,_,hm,_⟩:=s.exists_secondParabolic p B5 hi
  exact ⟨X,hm,s.compatible_fullRee_iso B5 hi X hm⟩

theorem compatible_fullRee_amalgam_of_typeRu (h:IsTypeRu G) :
    ∃(d:LocalSetup G)(p:Plane d)(s:SourceChoice p)
      (B5:Sylow 5 d.toTypeRuSetup.H)(X:Sylow 3 p.parabolic),
      (∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) ∧
      Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)) ∧
      ChapterF.Source.BinaryRee.LocalData (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X) ∧
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X)
          (p.T_F_le_F₁ B5) (p.T_F_le_F₂ B5 X))
        Tits.ExceptionalParabolics.FullRee.amalgam) := by
  obtain ⟨d,p,⟨s⟩⟩:=source_J4_choice h
  obtain ⟨B5,hi⟩:=s.inverts_sylow_five
  obtain ⟨X,hm,hiso⟩:=s.exists_compatible_fullRee_iso B5 hi
  exact ⟨d,p,s,B5,X,hi,hm,s.localData_of_second_quotient B5 hi X hm,hiso⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup
