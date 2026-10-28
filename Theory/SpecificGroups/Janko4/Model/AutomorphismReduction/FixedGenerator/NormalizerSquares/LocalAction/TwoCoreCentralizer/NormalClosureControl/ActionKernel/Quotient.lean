module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.CentralizerReduction

/-!
# Detecting the local action kernel by the actual outer action

For H = `localSubgroup` and its certified normal closure N, conjugation
induces H/N → Out(N). An upper bound on H/N and a matching lower bound
on this map's image force injectivity, which implies C_H(N) ≤ N.
These two finite bounds are independent obligations. This construction uses
the actual subgroup N, not an abstract group with the proposed local shape.

Source motivation: GLS3 Table 5.3i, printed p.270, the 2A centralizer entry.
The ATLAS words and matrix conventions are documented in `Max2Bridge`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The actual relative quotient by the seed normal closure. -/
abbrev LocalNormalClosureQuotient := localSubgroup ⧸ localNormalClosure

/-- The outer action induced by conjugation on the actual normal closure. -/
def localNormalClosureOuterAction : LocalNormalClosureQuotient →* MulAut.Outer localNormalClosure :=
  MulAut.outerAction localNormalClosure

theorem localNormalClosureOuterAction_mk (g : localSubgroup) :
    localNormalClosureOuterAction (QuotientGroup.mk g) =
      QuotientGroup.mk (localNormalClosureAction g) := rfl

/-- Injectivity of the outer action controls even elements outside N. -/
theorem localNormalClosureAction_ker_le_of_outer_injective
    (hi : Function.Injective localNormalClosureOuterAction) :
    localNormalClosureAction.ker ≤ localNormalClosure := by
  intro z hz
  apply (QuotientGroup.eq_one_iff z).mp
  apply hi
  rw [localNormalClosureOuterAction_mk, map_one]
  rw [show localNormalClosureAction z = 1 from hz]
  rfl

/-- A matching finite image lower bound makes the actual quotient action faithful. -/
theorem localNormalClosureOuterAction_injective_of_card_bounds
    (hupper : Nat.card LocalNormalClosureQuotient ≤ 2661120)
    (hlower : 2661120 ≤ Nat.card localNormalClosureOuterAction.range) :
    Function.Injective localNormalClosureOuterAction := by
  have hi := (localNormalClosureOuterAction.rangeRestrict_surjective.bijective_of_nat_card_le
    (hupper.trans hlower)).1
  intro a b hab
  apply hi
  exact Subtype.ext hab

/-- Conditional assembly; both numerical bounds must be proved for the literal model. -/
theorem localNormalClosureAction_ker_le_of_card_bounds
    (hupper : Nat.card LocalNormalClosureQuotient ≤ 2661120)
    (hlower : 2661120 ≤ Nat.card localNormalClosureOuterAction.range) :
    localNormalClosureAction.ker ≤ localNormalClosure :=
  localNormalClosureAction_ker_le_of_outer_injective
    (localNormalClosureOuterAction_injective_of_card_bounds hupper hlower)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
