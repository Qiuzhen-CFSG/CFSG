module

public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.TwoCore.Transport
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.TwoResidual

/-!
# Unique squares in the six-letter binary extension

The coordinate centralizer of the marked pair has two-residual W:A₄ and
embedded two-core W:V₄. The independently proved subgroup identities show
that every element of this core fixes coordinate 0 and that it contains the
displayed root whose square is the complementary weight-four vector.
The coordinate square calculation therefore gives exactly one square in the
marked coset of the constant line. Conjugation by actual A₆ actors, together
with the equality of the pair and complementary centralizers, gives the same
conclusion for every core vector with nonzero natural-module image.

All residual and two-core premises of the model calculation are discharged.
The application to an ambient M₂₂ cover still requires a marked isomorphism
with its fixed-hexad preimage; that recognition is separate mathematics.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

public section

open Theory.GroupTheory
namespace BinaryPermutation.SixCoreExtension

/-- The literal embedded O₂(O²(C(pair))) is W:V₄. -/
theorem residualCore_pair :
    centralizerResidualCore (vector (Multiplicative.ofAdd pair)) = pairCore :=
  residualCore_pair_of_residual_identity centralizerTwoResidual_pair

/-- Every element of the actual residual core fixes the first marked coordinate. -/
theorem residualCore_pair_fixes_zero (x : Model)
    (hx : x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd pair))) :
    x.right.val 0 = 0 := by
  rw [residualCore_pair] at hx
  exact hx.1.2.2.1

/-- The displayed square root belongs to the actual residual core. -/
theorem root_mem_residualCore_pair :
    root ∈ centralizerResidualCore (vector (Multiplicative.ofAdd pair)) := by
  rw [residualCore_pair]
  exact root_mem_pairCore

/-- The marked central coset contains exactly one square from its residual core. -/
theorem unique_square_pair :
    ∃! w : Model, (vector (Multiplicative.ofAdd pair))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd pair)), x ^ 2 = w :=
  unique_square_fiber_pair residualCore_pair_fixes_zero root_mem_residualCore_pair

/-- Every nonconstant core vector has a unique square lift from the literal
O₂(O²(C(t))) in its coset of the distinguished constant line. -/
theorem unique_square (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃! w : Model, (vector (Multiplicative.ofAdd v))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd v)), x ^ 2 = w :=
  unique_square_all_of_pair unique_square_pair v hv

end BinaryPermutation.SixCoreExtension
