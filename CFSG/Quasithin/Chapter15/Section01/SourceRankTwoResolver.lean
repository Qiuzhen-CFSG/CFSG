module
public import CFSG.Quasithin.Chapter15.Section01.SourceTheorem1513
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625

/-!
# The literal 15.1.3 consumer of the 14.6 terminal argument

Each selected M retains its original ordering-maximal and rank-two hypotheses.
The source plane and centralizer quotient are reconstructed by 14.6, and the
common terminal contradiction resolves its abelian branch. The nonabelian
reduction, rank-three theorem and terminal witness remain explicit source
inputs, to be discharged by their independent producers.
Source: Aschbacher--Smith, 15.1.3, printed pp.1086--1089.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 Chapter12.Section08 Chapter14.SourcePreliminaries
open Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The actual rank-two resolver, conditional only on the three remaining
source families. In particular the singleton centralizer hypothesis is kept. -/
theorem source_rankTwoResolver_of_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnonabelian : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
      ClassificationModels.IsTheoremEModel G)
    (hthree : ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab)
    (hwitness : ¬ ClassificationModels.IsTheoremEModel G → ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) :
    RankTwoResolver T Mc := by
  intro M hM hne hrank
  exact source_theorem_14_6_25_of_source_inputs hG T hempty hM hunique hmany hrank
    (hnonabelian M hM hne hrank) (hthree M hM hne) (fun hnot => hwitness hnot M hM hne)

end CFSG.Quasithin.Chapter15.Section01
