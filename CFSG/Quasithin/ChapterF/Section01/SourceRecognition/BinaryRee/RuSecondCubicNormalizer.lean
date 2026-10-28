module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Noncentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Image
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient.Overgroups

/-!
# The actual second-endpoint cubic normalizer

The original cubic marking gives a faithful order-48 subgroup of the native
order-96 normalizer, containing the canonical inner subgroup of order 24.
The source S₃ quotient excludes the central case of the native census, so
one of the two native reflection actors has a literal source lift. The
subsequent F.1.12 endpoint argument rules out the twisted actor using the
original involution census; no endpoint isomorphism is assumed here.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 theorem SecondCubicMarking.exists_native_actor {B5:Sylow 5 d.toTypeRuSetup.H}
    (m:SecondCubicMarking (p:=p) B5) (s:SourceChoice p)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃n:secondCubicNormalizer B5 m.X,
      secondCubicNormalizerAction B5 m.X m.coordinates n=CubicAction.inverter ∨
      secondCubicNormalizerAction B5 m.X m.coordinates n=CubicAction.twist*CubicAction.inverter := by
  rcases CubicAction.order48_subgroup_centralizes_or_actors
    (secondCubicNormalizerAction B5 m.X m.coordinates).range
    m.image_le_normalizer m.innerCore_le_image (m.image_card s hi) with hc|hb|hb
  · exact False.elim (m.image_not_le_centralizer s hi (fun a ha=>mem_centralizer_singleton_iff.mpr (hc a ha).eq))
  · obtain ⟨n,hn⟩:=hb
    exact ⟨n,Or.inl hn⟩
  · obtain ⟨n,hn⟩:=hb
    exact ⟨n,Or.inr hn⟩

 theorem SourceChoice.exists_faithful_second_cubic_normalizer (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃m:SecondCubicMarking (p:=p) B5,
      Function.Injective (secondCubicNormalizerAction B5 m.X m.coordinates) ∧
      Nat.card (secondCubicNormalizer B5 m.X)=48 ∧
      Nat.card (secondCubicNormalizerAction B5 m.X m.coordinates).range=48 ∧
      (secondCubicNormalizerAction B5 m.X m.coordinates).range≤CubicAction.cubicNormalizer ∧
      CubicAction.cubicInnerCore≤(secondCubicNormalizerAction B5 m.X m.coordinates).range ∧
      ¬(secondCubicNormalizerAction B5 m.X m.coordinates).range≤
        centralizer ({CubicAction.cubic}:Set (MulAut firstParabolicCore)) := by
  obtain ⟨m⟩:=s.secondCubicMarking_nonempty B5 hi
  exact ⟨m,m.action_injective,m.normalizer_card s hi,m.image_card s hi,
    m.image_le_normalizer,m.innerCore_le_image,m.image_not_le_centralizer s hi⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup
