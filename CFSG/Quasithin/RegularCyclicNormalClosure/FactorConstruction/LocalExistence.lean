module

public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.StepTwo
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Exhaustion
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.SupportRigidity

/-!
# Unconditional local exceptional construction

GLS C.14.2 Step 2 is now applied to the actual maximal-intersection
quotient. The ambient input excludes its first three alternatives; the
proved odd terminal supplies the exceptional local candidate. Thus the
local construction has no remaining geometry or solvability premise.
In particular, an actor whose order is not three commutes with all its
conjugates and itself supplies the full factor seed.

The order-three branch still requires compatibility of distinct exceptional
conjugates. No theorem here asserts that missing clause. The odd terminal
is used above Theory, without promoting the Feit--Thompson dependency closure
or asserting an unconditional lower-Theory factor theorem.

Sources: GLS Number 2 C.14.2, printed pp.85--89; Aschbacher--Smith E.6.24,
printed p.255. The unavailable Aschbacher 1981 10.4 proof is not claimed as
an audited source.
-/

public section

open Module Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open Representation.RegularCyclicNormalClosure.FactorConstruction
namespace CFSG.Quasithin.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- The noncommuting branch yields the actual pointwise fixer of a globally
maximal intersection, with every exceptional local clause. -/
theorem exists_exceptionalPointwiseFixer (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∃ a : A,
      (¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) ∧
      let F := fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)
      (∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
        finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤ finrank (ZMod 2) F) ∧
      ExceptionalCandidate ρ C (pointwiseFixer ρ F) := by
  obtain ⟨a, hnc, hmax, hlocal, _, _⟩ := h.exists_local_quotient hex
  let F := fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)
  let : Finite (W ⧸ F) := Finite.of_surjective F.mkQ F.mkQ_surjective
  exact ⟨a, hnc, hmax,
    exceptionalCandidate_of_stepTwo h a hnc F rfl hmax hlocal hlocal.geometric_alternatives⟩

/-- Local exceptional existence with all source premises discharged.
This is a candidate, not a full seed: global cross-fixation remains. -/
theorem exists_exceptionalCandidate (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∃ B : Subgroup A, ExceptionalCandidate ρ C B := by
  obtain ⟨a, _, _, hB⟩ := exists_exceptionalPointwiseFixer h hex
  exact ⟨_, hB⟩


/-- The constructed exceptional candidate is both the full pointwise fixer
of its fixed space and the full subgroup acting trivially modulo its moved
space. The two equalities concern the original ambient representation. -/
theorem exists_exceptionalCandidate_with_fixers (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∃ B : Subgroup A, ExceptionalCandidate ρ C B ∧
      pointwiseFixer ρ (fixedSpace ρ B) = B ∧
      quotientFixer ρ (displacementSpan ρ B ⊤) = B := by
  obtain ⟨a, _, _, hB⟩ := exists_exceptionalPointwiseFixer h hex
  refine ⟨_, hB, ?_, hB.quotientFixer_moved_eq h⟩
  rw [fixedSpace_pointwiseFixer_intersection a _ rfl]

/-- Only order three can give a noncommuting pair of cyclic actor conjugates. -/
theorem commuting_conjugates_of_card_ne_three (h : Input ρ C) (hC : Nat.card C ≠ 3) :
    ∀ a : A, ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d := by
  intro a
  by_contra hn
  obtain ⟨B, hB⟩ := exists_exceptionalCandidate h ⟨a, hn⟩
  exact hC hB.cyclic_card

/-- The full seed construction away from the exceptional actor order. -/
theorem factorSeed_of_card_ne_three (h : Input ρ C) (hC : Nat.card C ≠ 3) :
    FactorSeed ρ C C :=
  h.factorSeed_of_commuting_conjugates (commuting_conjugates_of_card_ne_three h hC)

end CFSG.Quasithin.RegularCyclicNormalClosure
