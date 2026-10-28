module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalGeneration
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Attainment
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
/-!
# Positive generation for the original SQTK minimal parabolic

Solvable groups have rank-one E-generation. Otherwise the original source
selects a genuine C-component generating H with the prescribed Sylow.
The normal case uses the full known-simple source families; the exchanged
case uses the actual two-factor argument. Both retain and lift through the
full solvable maximal core. Thus every original minimal parabolic has a
positive attained generation witness, without a model or numerical premise.

The known-simple corollary discharges Theorems A and C. The subgroup
application retains the original Sylow restriction and supplies exactly the
local input of the E.1.12 minimal-parabolic generation theorem.
Source: Aschbacher–Smith E.1.11–12 and E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem source_minimalParabolic_generation_exists
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f H := by
  classical
  by_cases hs : Group.IsSolvable H
  · let := hs
    exact ⟨1,by decide,isEGenerated_one_of_solvable⟩
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hH T hP hs
  by_cases hn : K.Normal
  · let := hn
    exact Section06.FixedPointBounds.ParabolicCartan.MarkedModels.source_normal_generation_exists
      hA hC hH T hP hs K hK hgen
  · exact Structure.NumericalBounds.paired_exists_isEGenerated hA hH T hP hs K hK hgen hn

/-- The original minimal-parabolic generation witness with every classification
input discharged by the full known-simple catalogue. -/
theorem source_minimalParabolic_generation_knownSimple
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f H :=
  source_minimalParabolic_generation_exists ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP

/-- Literal intrinsic minimal parabolics of any actual SQTK group, retaining
its prescribed Sylow and the same subgroup carrier. -/
theorem source_intrinsic_minimalParabolic_generation_knownSimple
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (P : Subgroup H) (hP : ChapterB.IsMinimalParabolicOver T P) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f P :=
  source_minimalParabolic_generation_knownSimple (hH.subgroup P)
    (T.subtype hP.1.1.le)
    (Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T P hP)

end CFSG.Quasithin.ChapterE
