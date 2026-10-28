module

public import Theory.Mathieu.M12.A5Fixer.Inputs
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# Local calculations for the full automorphism group of M₁₂

The setwise stabilizer of the marked Sylow two-subgroup maps onto Out(M₁₂).
Its kernel contains the 64 distinct inner automorphisms induced by that
Sylow subgroup. Thus a bound of 128 on this stabilizer suffices for the
outer-index bound.

For the order-four fixed-subgroup calculation, Cauchy's theorem and Sylow
five conjugacy reduce to automorphisms fixing one marked element of order
five. An exponent dividing ten for this fixer excludes order four.

The two propositions below are concrete obligations, not asserted results.
They concern the full abstract automorphism group of the Witt-design carrier.
Source context: Aschbacher–Smith 16.1.5(4), 16.1.7(3f), and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms
open M12SmallPair
open scoped Pointwise

/-- The setwise stabilizer in the full abstract automorphism group. -/
noncomputable def sylowStabilizer : Subgroup (MulAut M12) :=
  MulAction.stabilizer (MulAut M12) sylowCandidate

/-- The remaining local cardinality calculation for the outer-index bound. -/
def SylowStabilizerBound : Prop := Nat.card sylowStabilizer ≤ 128

/-- A concrete element of order five, written in the existing marked actors. -/
noncomputable def fiveElement : M12 :=
  cubicActor * movingActor * cubicActor * movingActor * rightI

theorem fiveElement_order : orderOf fiveElement = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime <;> decide +kernel

/-- A local exponent calculation sufficient to exclude fixed five-subgroups.
No restriction to inner automorphisms is imposed. -/
def FiveFixerExponent : Prop :=
  ∀ a : MulAut M12, a fiveElement = fiveElement → a ^ 10 = 1

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
