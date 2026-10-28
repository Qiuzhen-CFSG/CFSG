module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Inputs
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Suzuki recognition of the original three-free C-component quotient

The completed Theorems A and C supply A.3.6 on the actual ambient two-core
quotient. Every nonsuzuki alternative has a three divisor. The catalogue
therefore recognizes the component's literal quotient by its own two-core
as a Suzuki group, and hence as a Bender group.

Source: Aschbacher--Smith, 10.3.3, printed p.756, using A.3.6, pp.43--45.
The catalogue deduction is reused from SuzukiIsolation.Catalogue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
universe u

/-- Three-freeness recognizes the actual two-core quotient, with no classification premise. -/
theorem threeFreeRecognition {H : Type u} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (I : Subgroup H) (hI : I.IsCComponent) (h3 : ¬ 3 ∣ Nat.card I) :
    ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 H)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  obtain ⟨m, hm, e⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.component_suzuki_quotient
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      hQ hI (Nat.prime_three.coprime_iff_not_dvd.mpr h3)
  exact .suzuki m hm e

/-- The exact intrinsic recognition contract used by the normal-seed assembly. -/
theorem threeFreeRecognitionInput : ThreeFreeRecognitionInput.{u} := by
  intro H _ _ hH I hI h3
  exact threeFreeRecognition hH I hI h3

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
