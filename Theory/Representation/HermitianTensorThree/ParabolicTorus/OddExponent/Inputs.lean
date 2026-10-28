module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Contracts
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions

/-!
# Natural matrix inputs for the odd parabolic exponent

The Hermitian normalizer calculation reduces the odd, fixed-field linear
case to a GL₃ congruence. Two independent matrix calculations finish the
argument: recovering the marked natural subspace from normalization of its
image parabolic, and bounding the odd order of a matrix preserving that
subspace. The latter includes nonsplit two-dimensional blocks.

These are explicit input contracts, not proofs of the calculations. Their
consumer is `oddLinearParabolicExponent_of_matrix_inputs` in `OddExponent`.
The coefficient, central-kernel, and arbitrary-conjugate reductions are
proved there without additional source assumptions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup,
printed p.380, and Proposition 8.2.3, printed pp.715–716.
-/

@[expose] public section
noncomputable section

namespace Representation.HermitianTensorThree.ParabolicTorus.OddExponent
open ImageOuter
variable (n : ℕ) [NeZero n]

/-- The two block shapes are precisely preservation of the marked natural
point and marked natural plane, respectively. -/
def NaturalParabolicShape (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) : Prop :=
  (g.val 1 0 = 0 ∧ g.val 2 0 = 0) ∨
  (g.val 2 0 = 0 ∧ g.val 2 1 = 0)

/-- Recover natural-space geometry from normalization of the literal image
parabolic. The congruence action has its original norm-one scalar kernel. -/
def CongruenceParabolicRecovery : Prop :=
  ∀ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
    (binaryCongruence n g ∈ Subgroup.normalizer
        (pointParabolicImage n : Set (BinaryAut n)) ∨
      binaryCongruence n g ∈ Subgroup.normalizer
        (planeParabolicImage n : Set (BinaryAut n))) →
    NaturalParabolicShape n g

/-- The odd exponent of both natural GL₃ parabolics over GF(2^(2n)).
The factor `2^(4*n)-1` allows a nonsplit two-dimensional block. -/
def NaturalParabolicOddExponent : Prop :=
  ∀ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
    Odd (orderOf g) → NaturalParabolicShape n g →
      orderOf g ∣ 2 ^ (4 * n) - 1

end Representation.HermitianTensorThree.ParabolicTorus.OddExponent
