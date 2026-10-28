module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourReduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourcePresentationRecognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SolvableAssembly

/-!
# The remaining L₂(8) obstruction to original terminal solvability

The certified J₃ recognition excludes the normalized degree-four A₅ branch
under the original hypotheses. Thus every nonsolvable terminal factor supplies
an actual lifted L₂(8) component. Its exclusion implies terminal solvability
and, using the proved self-centralization, nonfusion, and core-collapse
theorems, the original nonabelian Theorem E conclusion.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable {G : Type*} [Group G] [Finite G]

/-- Outside the Theorem E models, an original nonsolvable terminal factor
has a lifted L₂(8) component. No auxiliary module instances are assumed. -/
theorem source_eight_of_terminal_nonsolvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ EightImageRow F K := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let := rankTwoSeed_elementary h
  obtain ⟨_,he,hx,B,v,hyp,_⟩ := Recognition.rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  let := hx
  obtain ⟨K,hK,⟨hspan,⟨e5⟩,hd⟩ | h8⟩ :=
    source_normalized_a5_four_or_eight hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hn
  · exact (source_single_a5_j3_excluded_of_four hG T hempty hM hu hmany hcard e
      F hne hnot g hgP hgH hyp hK e5 hspan hd).elim
  · exact ⟨K,hK,h8⟩

/-- The original terminal-solvability reduction with the J₃ branch discharged. -/
theorem source_terminal_solvable_of_eight_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  by_contra hn
  obtain ⟨K,hK,h8⟩ := source_eight_of_terminal_nonsolvable hG T hempty hM hu hmany
    hcard e hnot F hne g hgP hgH hn
  exact height K hK h8

/-- The original nonabelian Theorem E conclusion now needs only exclusion
of the actual lifted L₂(8) terminal components. -/
theorem source_theoremE_of_nonabelian_of_eight_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (height : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
      ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_solvable hG T hempty hM hu hmany hrank ?_ hne
  intro hnot F hneF g hgP hgH
  obtain ⟨hcard,⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  exact source_terminal_solvable_of_eight_exclusion hG T hempty hM hu hmany hcard e
    hnot F hneF g hgP hgH (height hnot F hneF g hgP hgH)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
