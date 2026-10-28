module
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.Split
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.TwistedE6
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.Triality
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.Ree

/-!
# Exceptional known-simple carriers have order divisible by three

The full catalogue's exceptional models are handled at every allowed parameter,
using literal isomorphisms to their concrete carriers. Split and graph-field
families contain one opposite root pair whose cubic survives the central
quotient. Small Ree uses its root subgroup; large Ree uses its constructed
local root blocks; G2 uses its actual rank-one subgroup.

These statements remove the exceptional branches in the known-simple
prime-to-fifteen solvability argument. No finite-simple guard, order formula,
subsystem recognition, or additional model input is assumed.
Source: the model catalogue from GLS3 Theorem 2.2.7 and Sections 2.4–2.6.
-/
public section
namespace CFSG.KnownSimple
variable {G : Type*} [Group G]

theorem IsG2Carrier.three_dvd_card (h : IsG2Carrier G) : 3 ∣ Nat.card G := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Theory.SpecificGroups.ThreeDivisibility.g2 F

theorem IsExceptionalExtensionModel.three_dvd_card
    (h : IsExceptionalExtensionModel G) : 3 ∣ Nat.card G := by
  cases h with
  | f4 q h =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact ExceptionalSplit.f4_three_dvd_card F
  | e6 q h =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact ExceptionalSplit.e6_three_dvd_card F
  | e7 q h =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact ExceptionalSplit.e7_three_dvd_card F
  | e8 q h =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact ExceptionalSplit.e8_three_dvd_card F
  | twistedE6 q h =>
    obtain ⟨p, m, hp, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact TwistedE6.model_three_dvd_card p m
  | reeG2 q h =>
    obtain ⟨m, F, hF, hfin, hchar, hp, _, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact Atlas.ReeG2.three_dvd_card_model F m hp.cardinality
end CFSG.KnownSimple

namespace Triality.Standard

theorem IsTrialityGroup.three_dvd_card {G : Type*} [Group G]
    (h : IsTrialityGroup G) : 3 ∣ Nat.card G := by
  obtain ⟨P, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact PrimeToFifteen.three_dvd_card P
end Triality.Standard

namespace ReeF4

theorem IsReeF4Model.three_dvd_card {G : Type*} [Group G]
    (h : IsReeF4Model G) : 3 ∣ Nat.card G := by
  obtain ⟨m, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_model m
end ReeF4
