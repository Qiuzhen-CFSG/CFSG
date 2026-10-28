module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift.Action
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift.CubeLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift.Scalar
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift.TorsionBound

/-!
# Abelian lifts and the full projective pair action

The cube-one subgroup of an abelian SU₃ preimage supplies an intrinsic
projective line. Every ambient automorphism lifts multiplicatively through
the actual projection, so the line is invariant under the whole pair
automizer, including outer automorphisms. The scalar kernel has order three,
and the determinant-one cubic torsion bound forces the projective line to
have order three inside the elementary subgroup of order nine.

The theorem `abelian_lift_reducibility` discharges every input for p > 3
and p ≡ 2 modulo three. The Sylow-product hypothesis is retained by the
published contract; this route gives a common invariant line without using
that additional restriction.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); compare A.3.21(c), printed pp.55–56.
-/

public section
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary

/-- Conditional assembly from the remaining determinant-one torsion bound.
All scalar-kernel, full-automorphism and Frattini-quotient steps are discharged. -/
theorem abelian_lift_reducibility_of_cube_bound (p : ℕ) (hp : p.Prime)
    (ho : Odd p) (hmod : p % 3 = 2) (hbound : AbelianLift.CubicTorsionBound p) :
    AbelianLiftReducibility p := by
  intro E _ _ J hs hfield hconj T U he hU hab _hperm
  let _ := hs
  let _ := hab
  apply AbelianLift.reducible_of_cubeOneImage_card J U he hU
  · exact AbelianLift.cubeOneImage_card_three J U he hU
      (AbelianLift.scalar_kernel_card J hmod hfield hconj)
      (hbound J hfield hconj U)
  · exact AbelianLift.automorphism_lifts J hp ho hfield hconj

/-- An elementary subgroup of order nine with abelian full SU₃ preimage is
reducible under every two-subgroup of the full projective pair automizer. -/
theorem abelian_lift_reducibility (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hp3 : 3 < p) (hmod : p % 3 = 2) : AbelianLiftReducibility p :=
  abelian_lift_reducibility_of_cube_bound p hp ho hmod
    (AbelianLift.cubic_torsion_bound hp hp3)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary
