module

public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.LocalExistence
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.PairBound
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ExceptionalCompatibility

/-!
# Original cyclic-normal-closure source assembly

This is the Aschbacher--Smith E.6.24 source interface for the actual regular
cyclic input. If the cyclic actor has order other than three, the commuting
branch supplies its original subgroup as the factor seed. In the order-three
branch, the local exceptional candidate from the maximal-intersection source
is retained, and the checked noncommuting pair bound supplies the
`ExceptionalCandidate` compatibility theorem. The result uses the literal
ambient representation and subgroup marking; no TI fixed-space premise is
introduced.

Source: Aschbacher, Weak closure in finite groups of even characteristic,
J. Algebra 70 (1981), 10.4, as used in Aschbacher--Smith E.6.24, printed
p.255. The separate GLS C.14.2 TI statement is not used here.
-/

public section

open Module Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open Representation.RegularCyclicNormalClosure.FactorConstruction
namespace CFSG.Quasithin.RegularCyclicNormalClosure

variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- The original Input always yields a marked factor seed.

The noncommuting order-three branch applies the finite pair theorem to the
actual candidate returned by `exists_exceptionalCandidate`; its resulting
seed keeps that same subgroup `B`.
-/
theorem exists_factorSeed_of_input (h : Input ρ C) :
    ∃ B : Subgroup A, FactorSeed ρ C B := by
  classical
  by_cases hC3 : Nat.card C = 3
  · by_cases hc : ∀ a : A, ∀ c ∈ C,
      ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d
    · exact ⟨C, h.factorSeed_of_commuting_conjugates hc⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hc
      obtain ⟨B, hB⟩ := exists_exceptionalCandidate h ⟨a, ha⟩
      refine ⟨B, hB.factorSeed_of_pair_bound h ?_⟩
      intro a b hab
      exact h.conjugates_moved_finrank_le_three hC3 a b hab
  · exact ⟨C, factorSeed_of_card_ne_three h hC3⟩

end CFSG.Quasithin.RegularCyclicNormalClosure
