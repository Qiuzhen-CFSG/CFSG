module
public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.Completion
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SmallFromCommutingFives
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.Recognition

/-!
# Original J.4–J.5 recognition: FullRee

The genuine fixed-five placement proves Small for the same original
completion. Full F.4.8 then recognizes the literal generated subgroup F,
preserving the first and second endpoint embeddings and their common T_F.
There is no model equivalence or abstract action premise. Placement is the
earlier source j/six-cycle conclusion, retained by the assembly owner.

Source: Aschbacher–Smith J.4.7–10 and J.5.1–14, printed pp.442–449.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices FiveHexagon.MarkedInverter FiveHexagon.PathTransport
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 theorem SourceChoice.fullRee_of_fixedFive_placement (s:SourceChoice p) (c:Centralizers.Choices d)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (q:Completion (p.F B5 X)) (e:first≃*p.F₁ B5) (e₂:second≃*p.F₂ B5 X)
    (hl:∀a:first,(q.left a:G)=(e a:G)) (hr:∀a:second,(q.right a:G)=(e₂ a:G))
    (hz:(e modelZ:G)=c.z)
    (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    (hplace:FiveHexagon.fixedFive B5 (sourceU e)≤
      (stabilizer q.family (completionFourthWord q•basePoint q)).map (p.F B5 X).subtype) :
    ∃E:p.F B5 X≃*ReeF4.Model 0,
      ((p.F₁ B5).subgroupOf (p.F B5 X)).map E.toMonoidHom=first ∧
      ((p.T_F B5).subgroupOf (p.F B5 X)).map E.toMonoidHom=B ∧
      ((p.F₂ B5 X).subgroupOf (p.F B5 X)).map E.toMonoidHom=second ∧
      (∀a:first,E (q.left a)=(a:ReeF4.Model 0)) ∧
      (∀a:second,E (q.right a)=(a:ReeF4.Model 0)) := by
  have hsmall:=ParabolicHexagon.SmallFromCommutingFives.source_small_of_fixedFive_placement
    q c B5 e (p.F B5 X).subtype (p.F B5 X).subtype_injective hl hz hfive hplace
  have hL:q.left.range=(p.F₁ B5).subgroupOf (p.F B5 X):=by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      change (q.left b:G)∈p.F₁ B5
      rw [hl]
      exact (e b).property
    · intro ha
      obtain ⟨b,hb⟩:=e.surjective ⟨a,ha⟩
      refine ⟨b,Subtype.ext ?_⟩
      exact (hl b).trans (congrArg (fun z:p.F₁ B5=>(z:G)) hb)
  have hR:q.right.range=(p.F₂ B5 X).subgroupOf (p.F B5 X):=by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      change (q.right b:G)∈p.F₂ B5 X
      rw [hr]
      exact (e₂ b).property
    · intro ha
      obtain ⟨b,hb⟩:=e₂.surjective ⟨a,ha⟩
      refine ⟨b,Subtype.ext ?_⟩
      exact (hr b).trans (congrArg (fun z:p.F₂ B5 X=>(z:G)) hb)
  have hT:q.middle.range=(p.T_F B5).subgroupOf (p.F B5 X):=by
    rw [←q.overlap,hL,hR]
    change (p.F₁ B5⊓p.F₂ B5 X).subgroupOf (p.F B5 X)=_
    rw [(s.localData_of_second_quotient B5 hi X hm).intersection]
  refine ⟨q.equivOfSmall hsmall,?_,?_,?_,q.equivOfSmall_left hsmall,q.equivOfSmall_right hsmall⟩
  · rw [←hL];exact q.equivOfSmall_left_map hsmall
  · rw [←hT];exact q.equivOfSmall_middle_map hsmall
  · rw [←hR];exact q.equivOfSmall_right_map hsmall
end CFSG.Quasithin.ChapterJ.RuSubgroup
