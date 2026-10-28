module
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.EvenParameter.FixedOrders
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.EvenParameter.OddModels
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.EvenParameter.JankoFour

/-!
# Reductions for the E2 signed projective-three parameter

The prime-field PSL₂ alternative is excluded by the supplied three-rank
hypothesis. The PSL₃(3) alternative has quotient order at most 5616, forcing
q = 2 under the source congruence. Seven sporadics are excluded by exact
carrier orders; J₄ has a certified elementary two-subgroup of order 2¹¹.

The final theorem here is conditional on two still separate intrinsic model
facts: the elementary two-subgroup bound for odd-field projective-three groups,
and large elementary subgroups or the five small orders for the remaining E2
models. It is not the unconditional parameter theorem or Lemma 16.4.5.
Both premises must be discharged in this module's final assembly. No premise
assumes a field characteristic, parameter exclusion, or desired conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E2, pp.1169–1170,
A.3.18(2), pp.51–52, and Lemma 16.4.5, p.1184. The original q and sign
are preserved throughout. This extension never imports the section assembly.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Subgroup Theory.GroupTheory Chapter1.Section02.LocalModels
open scoped MatrixGroups

variable {L : Type*} [Group L] [Finite L] {unitary : Bool} {q : ℕ}

/-- A quotient of the E2 model PSL₃(3) is too small for a parameter above two. -/
theorem parameter_eq_two_of_linear_three_three
    (hL : ClassicalGroup.IsPSL L 3 3)
    (hm : IsPSLSign (L ⧸ pCore 2 L) unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) : q = 2 := by
  have hcard : Nat.card L = 5616 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
    have ho := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
    rw [← Nat.card_congr e.toEquiv, hF] at ho
    norm_num at ho
    exact ho
  apply parameter_eq_two_of_small_card hm hc
  rw [← hcard]
  exact Nat.le_of_dvd Nat.card_pos (pCore 2 L).card_quotient_dvd_card

/-- The unresolved model families after the completed rank and order comparisons. -/
theorem evenType_parameter_reduction (hr : 1 < primeRank 3 L)
    (he : IsEvenTypeComponent L)
    (hm : IsPSLSign (L ⧸ pCore 2 L) unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) :
    (∃ n : ℕ, 0 < n ∧ q = 2 ^ n) ∨
    IsEvenTypeLieQuotient (L ⧸ pCore 2 L) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Janko4.Model) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Rudvalis.Model) := by
  rcases he with hlie | hthree | ⟨p, hp, htwo⟩ | hsporadic
  · exact Or.inr (Or.inl hlie.1)
  · exact Or.inl ⟨1, by decide, by simpa using parameter_eq_two_of_linear_three_three hthree hm hc⟩
  · exact (not_lt_of_ge (prime_psl_two_threeRank_le_one hp.1 htwo) hr).elim
  · exact Or.inr (Or.inr (sporadic_remaining hsporadic hm hc))

/-- Conditional final assembly from intrinsic elementary-subgroup and order facts.
The unconditional parameter exclusion still requires both displayed premises. -/
theorem parameter_two_power_of_e2_invariants (hr : 1 < primeRank 3 L)
    (he : IsEvenTypeComponent L)
    (hm : IsPSLSign (L ⧸ pCore 2 L) unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1)
    (hodd : Odd q → ∀ E : Subgroup (L ⧸ pCore 2 L),
      IsElementaryAbelian 2 E → Nat.card E ≤ 4)
    (hmodels : IsEvenTypeLieQuotient (L ⧸ pCore 2 L) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* Rudvalis.Model) →
      (∃ E : Subgroup (L ⧸ pCore 2 L), IsElementaryAbelian 2 E ∧ 4 < Nat.card E) ∨
      Nat.card (L ⧸ pCore 2 L) = 60 ∨ Nat.card (L ⧸ pCore 2 L) = 168 ∨
      Nat.card (L ⧸ pCore 2 L) = 360 ∨ Nat.card (L ⧸ pCore 2 L) = 6048 ∨
      Nat.card (L ⧸ pCore 2 L) = 62400) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  rcases evenType_parameter_reduction hr he hm hc with hq | hlie | hj4 | hru
  · exact hq
  · exact parameter_two_power_of_elementary_alternatives hm hc hodd (hmodels (Or.inl hlie))
  · exact parameter_two_power_of_elementary_alternatives hm hc hodd
      (Or.inl (janko4_model_large_elementary hj4))
  · exact parameter_two_power_of_elementary_alternatives hm hc hodd (hmodels (Or.inr hru))

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter
