module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.PairSource
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.UnitaryException

/-!
# Closing the two-component source branch once its models are identified

The generic source deductions construct the common center, intersection,
ambient generation and original central quotient. The concrete unitary
calculation then supplies the exceptional three-rank and gcd condition.
Thus two centered components identified as the odd-degree binary SU₃
models contradict the original failure of Theorem A.

The only model premises are the two literal component identifications;
the local-rank model sieve is responsible for constructing those.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.not_two_centered_unitary_components
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥)
    (hcmodel : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel C 3 (2 ^ n))
    (hdmodel : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel D 3 (2 ^ n)) : False := by
  have hp := h.prime_eq_three_of_semisimple_not_quasisimple ih hsemi hn hcovers
  subst p
  obtain ⟨hg, he, hi, hcard⟩ :=
    h.centered_component_pair_structure ih hsemi hn hcovers hC hD hne hzC hzD
  obtain ⟨e⟩ := h.section_equiv_centerQuotient_of_center_card_three ih.theoremA hsemi hcard
  obtain ⟨n, hnlarge, hnodd, hnmodel⟩ := hcmodel
  obtain ⟨m, hmlarge, hmodd, hmmodel⟩ := hdmodel
  have hc : C ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hne)
  let d : OddCenterCovers.UnitaryCentralProductData G := {
    first := C
    second := D
    distinct := hne
    first_quasisimple := hC.2
    second_quasisimple := hD.2
    commuting := hc
    product := by
      intro x
      have hx : x ∈ (C : Set G) * (D : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right C D
          (hc.trans (Subgroup.centralizer_le_normalizer _)), hg]
        trivial
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
    n₁ := n
    n₂ := m
    first_large := hnlarge
    second_large := hmlarge
    first_odd := hnodd
    second_odd := hmodd
    first_model := hnmodel
    second_model := hmmodel
    centers_eq := he
    intersection_eq := hi }
  exact h.not_unitary_central_product d hC hD e

end CFSG.Quasithin.ChapterA.Section02
