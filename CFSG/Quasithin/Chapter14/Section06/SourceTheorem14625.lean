module
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete
public import CFSG.Quasithin.ClassificationModels

/-!
# The original rank-two entry to the 14.6.25 assembly

The original rank-two hypothesis implies the order-four plane and the full
S₃ action of the selected M. The first isomorphism theorem identifies its
literal centralizer quotient; no new action or replacement M is chosen.

The source assembly separates the nonabelian reduction of 14.3.16 from the
two independent abelian inputs: terminal witness construction and the full
14.6.10(5) rank-three theorem. The terminal contradiction is already proved
on their exact original subgroups. These inputs are explicit pending source
proofs; witness construction retains the source counterexample assumption,
so this module does not claim an unconditional 14.6.25.
Source: Aschbacher--Smith, printed pp.994--1001 and 1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Conditional final source assembly. Each extra premise is a distinct source
obligation, not a replacement definition of classification. -/
theorem source_theorem_14_6_25_of_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hnonabelian : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
      ClassificationModels.IsTheoremEModel G)
    (hthree : ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab)
    (hwitness : ¬ ClassificationModels.IsTheoremEModel G → ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) :
    ClassificationModels.IsTheoremEModel G := by
  classical
  by_contra hnot
  have hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc) := by
    by_contra hnonab
    exact hnot (hnonabelian hnonab)
  obtain ⟨hcard,⟨e⟩⟩ := source_plane_of_rankTwo hrank
  exact source_terminal_contradiction hG T hempty hM hunique hmany hcard e hab
    (hthree hcard e hab) (hwitness hnot hcard e hab)

end CFSG.Quasithin.Chapter14.Section06
