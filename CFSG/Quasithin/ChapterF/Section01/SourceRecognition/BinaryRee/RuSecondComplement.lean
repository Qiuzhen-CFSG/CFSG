module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondComplement.Bad
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondComplement.Inverter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondComplement.Marking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Noncentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Image
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient

/-!
# The complete original second-parabolic recognition

The actual cubic normalizer has faithful image of order 48 containing the
native inner-cubic subgroup of order 24. The proved three-line quotient census
leaves a centralizing subgroup, the genuine reflection, or the twisted actor.
The original S₃ quotient excludes centralization; the original involution
count excludes the twisted actor. The remaining faithful lift provides the
native involutory inverter and hence the whole endpoint equivalence.

The selected X, original A, and literal F₂ are retained throughout. No endpoint
model, complement, action-faithfulness, or finite-census conclusion is assumed.
Source: the binary Ree branch of Aschbacher–Smith F.1.12 and J.4.5.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.inverter_mem_range (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (m:SecondCubicMarking (p:=p) B5) :
    CubicAction.inverter∈(secondCubicNormalizerAction B5 m.X m.coordinates).range := by
  rcases CubicAction.order48_subgroup_centralizes_or_actors
    (secondCubicNormalizerAction B5 m.X m.coordinates).range
    m.image_le_normalizer m.innerCore_le_image (m.image_card s hi) with hc|hb|hbad
  · exfalso
    exact m.image_not_le_centralizer s hi (fun α hα=>mem_centralizer_singleton_iff.mpr (hc α hα))
  · exact hb
  · exact (s.badActor_not_mem_range B5 hi m hbad).elim

theorem SourceChoice.F₂_equiv_fullRee_second (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    Nonempty ((p.F₂ B5 X)≃*Tits.ExceptionalParabolics.FullRee.second) := by
  obtain ⟨m,hmX⟩:=s.secondCubicMarking_with_X B5 hi X hm
  obtain ⟨E,_⟩:=s.F₂_equiv_of_inverter_mem_range B5 hi m (s.inverter_mem_range B5 hi m)
  exact ⟨(MulEquiv.subgroupCongr (congrArg (p.F₂ B5) hmX.symm)).trans E.symm⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
