module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ModelInput
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.SourceConfigurations
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FiveGeometry

/-!
# The degree-five chosen-orbit weak-closure implications

H.9.2(5) and E.3.32 exclude the actual corank-two offender, giving w > 2
from w > 1 and r ≥ 7. At corank one the same argument leaves only
automizer rank four; its vanishing pure intersection is retained.

The model input is a compatible source action on the actual automizer. Its
construction, the rank-four first-stage contradiction, and the degree-four
argument remain separate obligations of the complete 12.1.8/10 assembly.
Source: Aschbacher--Smith, 12.1.8 and 12.1.10, pp.792--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- The degree-five implication in 12.1.10, conditional on construction of
the compatible action model on the actual orbit. -/
theorem doubledFive_globalW_gt_two_of_many_of_model
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.MarkedAutomizerModel →
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    (7 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro M hw hr
  by_contra hf
  obtain ⟨g, _, _, hc⟩ := D.doubled_second_configuration_of_many h hmany B hw hr hf
  exact five_second_configuration_false M.setup M.representation_eq hc

/-- For degree five, the only surviving first-stage case has action-image
rank four. The same witness retains the source pure-intersection restriction. -/
theorem doubledFive_first_rank_four_of_many_of_model
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.MarkedAutomizerModel → B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (5 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    ¬ 1 < globalW (componentOrbit V (T : Subgroup G)) T →
    ∃ g : G,
      IsWOffenderAt (componentOrbit V (T : Subgroup G)) T g ∧
      globalW (componentOrbit V (T : Subgroup G)) T = 1 ∧
      ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 5 ∧
      rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
        (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)) = 4 ∧
      B.naturalSpace ⊓ subgroupSpace (componentOrbit V (T : Subgroup G))
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro M hp hw hr hf
  obtain ⟨g, hg, he, hc, hpure⟩ :=
    D.doubled_first_configuration_of_many h hmany B hp hw hr hf
  refine ⟨g, hg, he, hc, ?_, hpure⟩
  exact le_antisymm (five_first_rank_le_four M.setup M.representation_eq hc) hc.rank_lower

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
