module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.Source
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve

/-!
# At most one centered component in the source counterexample

Two distinct components with nontrivial centers have local three-rank at most
one by quasithinness. The complete covering catalogue and its local-rank sieve
identify both components as odd-degree binary SU₃ groups. The actual common
center, product and quotient markings then give the exceptional alternative
of Theorem A, contradicting the original counterexample.

This closes the two-centered-component branch without a prime-core identity,
an assumed covering list, or an assumed component-model identification.

Source: Aschbacher–Smith A.2.12(I)–(II), printed pp.36–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
variable (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
variable (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
variable (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
include h ih hsemi hn

theorem CounterexampleToTheoremA.source_centered_component_unitary_model
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel C 3 (2 ^ n) := by
  let := hC.2
  rcases h.component_center_card_and_coverModel ih hsemi hn
      SQTKStructure.OrdinarySource.remainingOddCoverInputs hC with he | ⟨hc, hm⟩
  · exact (hzC (card_eq_one.mp he)).elim
  · exact OddCenterCovers.unitary_model_of_threeCover_local_rank_le_one hm hc
      (h.source_component_local_threeRank_le_one ih hsemi hn hC hD hne hzC hzD)

theorem CounterexampleToTheoremA.source_not_two_centered_components
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) : False := by
  exact h.source_not_two_centered_unitary_components ih hsemi hn hC hD hne hzC hzD
    (h.source_centered_component_unitary_model ih hsemi hn hC hD hne hzC hzD)
    (h.source_centered_component_unitary_model ih hsemi hn hD hC hne.symm hzD hzC)

theorem CounterexampleToTheoremA.source_centered_components_eq
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) : C = D := by
  by_contra hne
  exact h.source_not_two_centered_components ih hsemi hn hC hD hne hzC hzD

end CFSG.Quasithin.ChapterA.Section02
