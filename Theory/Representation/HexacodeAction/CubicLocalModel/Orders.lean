module

public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.PointStabilizer
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.Intrinsic
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour

/-!
# The covered point commutator residual has cubic quotient

The stabilizer of any line in the actual binary natural module is a central
cubic extension of S₄, with no elements of order nine. A Sylow subgroup of
the cover contained in that stabilizer restricts to a Sylow subgroup there.
The intrinsic commutator residual and the model's embedded commutator
residual have isomorphic two-core quotients.
Applying the central cubic extension calculation inside that stabilizer
therefore gives order three for the model's commutator residual modulo its
intrinsic two-core, for every line stabilized by the supplied Sylow subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877.
-/

public section

namespace Representation.Hexacode.CubicLocalModel.Orders

/-- The point commutator residual of the actual hexacode cover has quotient
of order three by its intrinsic two-core. This is the `i = 1` cubic order
in Notation 13.2.1, for an arbitrary Sylow-stable natural-module line. -/
theorem commutatorResidual_quotient_card (W : Submodule (ZMod 2) Natural)
    (P : Sylow 2 H) (hdim : Module.finrank (ZMod 2) W = 1)
    (hP : (P : Subgroup H) ≤ stabilizer W) :
    Nat.card (commutatorResidual W P ⧸ pCore 2 (commutatorResidual W P)) = 3 := by
  rw [commutatorResidual_quotient_card_eq_intrinsic W P hP]
  exact intrinsicCommutatorResidual_quotient_card_of_central_cubic_s4
    (symmetricFourMap W hdim) (symmetricFourMap_surjective W hdim)
    (symmetricFourMap_kernel_card W hdim) (symmetricFourMap_kernel_central W hdim)
    (fun _ hx => stabilizer_cube_eq_one_of_ninth W hx) (P.subtype hP)

end Representation.Hexacode.CubicLocalModel.Orders
