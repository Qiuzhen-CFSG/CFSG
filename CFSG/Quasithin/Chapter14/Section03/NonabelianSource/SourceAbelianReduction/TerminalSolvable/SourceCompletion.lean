module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SourceTerminalSolvability
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelMarked
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRecognitionInterface

/-!
# Original terminal solvability and the nonabelian Theorem E branch

The actual eight-field component join supplies both the minimal parabolic and
its residual quotient. Its original triality recognition excludes that last
terminal row. Together with the proved J₃ exclusion this gives terminal
solvability and the original nonabelian conclusion, with no component,
comparison, or terminal-solvability premise remaining.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- An actual lifted eight-field terminal component recognizes the original
ambient group; the component's full kernel and original join are retained. -/
theorem source_eight_theoremE_of_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    ClassificationModels.IsTheoremEModel G := by
  obtain ⟨hH,_,⟨eR⟩⟩ := source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8
  exact EightLargeParabolic.SourceRecognitionInterface.source_eight_theoremE
    hG T hempty hM hu hmany hcard e (K ⊔ (T : Subgroup G)) hH eR

/-- Original terminal solvability, with both nonsolvable component rows
excluded by their original ambient recognition proofs. -/
theorem source_terminal_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_eight_exclusion hG T hempty hM hu hmany hcard e
    hnot F hne g hgP hgH
  intro K hK h8
  exact hnot (source_eight_theoremE_of_component hG T hempty hM hu hmany hcard e hK h8)

/-- The original nonabelian branch of Theorem E, with all terminal component,
self-centralization, fusion, and core-collapse inputs supplied internally. -/
theorem source_theoremE_of_nonabelian
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_eight_exclusion hG T hempty hM hu hmany hrank ?_ hne
  intro hnot F _ g _ _ K hK h8
  obtain ⟨hcard,⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  exact hnot (source_eight_theoremE_of_component hG T hempty hM hu hmany hcard e hK h8)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
