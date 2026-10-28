module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.EvenRankOne
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Alternating
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.G2Exclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceQuadratic
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Symplectic
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedSource
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Sporadic
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.SmallEven
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Odd
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Tits
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.NativeSource

/-!
# The complete marked B.4 source action catalogue

The original full Theorems A and C classify the simple central quotient.
Every family then uses its proved action recognition: the even rank-one,
linear, symplectic, alternating and binary G₂ cases retain their actual intertwiners.
The original involution of displacement at most two excludes the remaining
ordinary G₂, odd, triality, Ree and sporadic possibilities. The native A₆ degree theorem
discharges the last representation input. No family classifier is a premise.

This specialized source theorem preserves the complete B.4.2 action list and
all fourteen B.4.5 rows. The broader universal FullB45 interface is unchanged.
Source: Aschbacher–Smith B.4.2–5, Chapter K and 13.5.21, pp.86–87,451–460,923–924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem alternating_six_seven (h : ChapterK.Alternating.Input ρ KnownSimple.IsKnownSimple L) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L := by
  have hr := ChapterK.Alternating.recognition_of_branches
    (ChapterK.Alternating.sixRecognition_of_inputs ChapterK.Alternating.sixDegree_native_source
      ChapterK.Alternating.RecognitionInputs.Six.fourSpace
      ChapterK.Alternating.RecognitionInputs.Six.normalizer)
    ChapterK.Alternating.sevenRecognition ChapterK.Alternating.tripleSixDegree
    ChapterK.Alternating.tripleSevenExclusion ρ h
  cases ChapterK.Alternating.conclusion_of_recognized ρ h hr with
  | ff _ hs => exact Or.inl hs
  | sevenNatural _ a hq hc =>
    let a' : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
        (ρ.comp L.subtype) (QuasisimpleSource.alternatingNatural 7) :=
      ⟨a.groupEquiv,a.linearEquiv,a.intertwines⟩
    have hn : Module.finrank (ZMod 2) V = 6 := by
      rw [a.linearEquiv.finrank_eq]
      exact BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)
    exact Or.inr (.alternatingSeven a' hn hq hc)

theorem alternating_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : n ≤ 8) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L := by
  have hlo := SourceClassification.alternating_degree_ge_five h e
  have hcases : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · apply psl2_case h (r := 2) (by decide)
    exact ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  · exact alternating_six_seven
      ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,Or.inl ⟨e⟩⟩
  · exact alternating_six_seven
      ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,Or.inr ⟨e⟩⟩
  · exact Or.inl (SourceClassification.alternating_eight_case h e)


theorem odd_case (h : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    (hm : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L := by
  cases hm with
  | linear_two p e hp ho he hm =>
    rcases odd_pslTwo_theoremC_parameters_of_small_involution h t ht hr hp ho he hm with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.altFive_of_psl2_five (by simpa using hm)
      exact alternating_case h (by decide) eQ
    · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven (by simpa using hm)
      have hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ 1) :=
        ⟨ZMod 2,inferInstance,inferInstance,by norm_num,⟨eQ⟩⟩
      exact Or.inl (ChapterK.Linear.Recognition.SourceQuadratic.actionCase_of_quadratic_le_two
        ⟨inferInstance,inferInstance,h.sqtk,h.fitting,h.quasisimple,h.faithful,h.irreducible,h.smallCubic⟩
        1 (by decide) hquot hq)
    · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.altSix_of_psl2_nine (by simpa using hm)
      exact alternating_case h (by decide) eQ
  | linear_three p hp ho hm => exact (odd_pslThree_excluded_of_small_involution h hp ho hm t ht hr).elim
  | unitary_three p hp ho hm =>
    obtain ⟨e⟩ := ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_g2Derived_of_cubicRatio_le_two
      ρ L ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible⟩ hp ho hm h.smallCubic
    exact g2_binary_case h e

theorem case_of_theoremC (h : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    (hm : ChapterA.Section02.IsTheoremCModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L := by
  cases hm with
  | alternating n hn he => exact alternating_case h hn (Classical.choice he)
  | odd hm => exact odd_case h hq t ht hr hm
  | bender hm =>
    cases hm with
    | linear r hr he => exact psl2_case h hr he
    | unitary r hr he => exact Or.inr (unitary_table h hr he)
    | suzuki m hm he => exact Or.inr (suzuki_table h hm (Classical.choice he))
  | linear_binary n hn hm => exact Or.inl (SourceClassification.binary_linear_case h hn hm)
  | sporadic hm => exact sporadic_case_of_displacement_rank h hm t ht hr
  | rank_two n hm =>
    cases hm with
    | linear hn hm =>
      exact Or.inl (ChapterK.Linear.Recognition.SourceQuadratic.actionCase_of_quadratic_le_two
        ⟨inferInstance,inferInstance,h.sqtk,h.fitting,h.quasisimple,h.faithful,h.irreducible,h.smallCubic⟩
        n hn hm hq)
    | symplectic hn hm => exact Or.inl (symplectic_model_case h hq hn hm)
    | g2 hn hm => exact (g2_model_excluded_of_small_involution h hn hm t ht hr).elim
    | triality hn hm => exact (triality_excluded_of_small_involution h n hn hm t ht hr).elim
    | ree_f4 m hm _ he => exact (reeF4_excluded_of_small_involution h hm (Classical.choice he) t ht hr).elim
    | symplectic_derived _ he =>
      exact alternating_case h (by decide)
        ((Classical.choice he).trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived _ he => exact g2_binary_case h (Classical.choice he)
    | tits _ he => exact (SourceClassification.tits_exclusion h (Classical.choice he)).elim

theorem actionCase_of_small_involution (h : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨ TableB45 ρ L :=
  case_of_theoremC h hq t ht hr
    (SourceClassification.quotient_model_of_theoremsAC
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple h)
end CFSG.Quasithin.ChapterB.SmallRatioClassification
