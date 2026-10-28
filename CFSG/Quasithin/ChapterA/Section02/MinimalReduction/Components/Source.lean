module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.PairUnitary
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

/-!
# Unconditional covering inputs for the source component reduction

The full raw covering catalogue is proved independently of universal
Theorems A and C, including the Ree, Held and J₄ odd-center restrictions.
It discharges every auxiliary covering premise in the source component
reduction. The remaining hypotheses below are the original counterexample,
proper-section induction and the actual components or model identifications.

These deductions do not yet assert that every counterexample is
quasisimple: the nonsemisimple reduction, the local-rank model sieve and
the case with at most one centered component remain separate source steps.

Source: Aschbacher–Smith A.2.12(I)–(III), printed pp.36–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
variable (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
variable (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
variable (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
include h ih hsemi hn

theorem CounterexampleToTheoremA.source_component_simple_or_threeCover
    {C : Subgroup G} (hC : IsComponent G C) :
    IsSimpleGroup C ∨
      (Nonempty (center C ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel C) :=
  h.component_simple_or_threeCover ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC

theorem CounterexampleToTheoremA.source_center_isThreeGroup : IsPGroup 3 (center G) :=
  h.center_isThreeGroup_of_semisimple_not_quasisimple ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs

theorem CounterexampleToTheoremA.source_semisimple_prime_eq_three : p = 3 :=
  h.prime_eq_three_of_semisimple_not_quasisimple ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs

theorem CounterexampleToTheoremA.source_component_threeRanks_eq_two
    {C : Subgroup G} (hC : IsComponent G C) (hz : center C ≠ ⊥) :
    primeRank 3 C = 2 ∧ primeRank 3 (C ⧸ center C) = 2 :=
  h.component_threeRanks_eq_two ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC hz

theorem CounterexampleToTheoremA.source_component_local_threeRank_le_one
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) : twoLocalPrimeRank 3 C ≤ 1 :=
  h.component_local_threeRank_le_one_of_other_centered ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC hD hne hzC hzD

theorem CounterexampleToTheoremA.source_centered_component_pair_structure
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) :
    C ⊔ D = ⊤ ∧
      (center C).map C.subtype = (center D).map D.subtype ∧
      C ⊓ D = (center C).map C.subtype ∧ Nat.card (center G) = 3 :=
  h.centered_component_pair_structure ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC hD hne hzC hzD

theorem CounterexampleToTheoremA.source_not_two_centered_unitary_components
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥)
    (hcmodel : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel C 3 (2 ^ n))
    (hdmodel : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel D 3 (2 ^ n)) : False :=
  h.not_two_centered_unitary_components ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC hD hne hzC hzD hcmodel hdmodel

end CFSG.Quasithin.ChapterA.Section02
