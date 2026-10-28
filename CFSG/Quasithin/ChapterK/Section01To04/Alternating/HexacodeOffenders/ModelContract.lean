module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.Coordinates

/-!
# Remaining concrete calculations for K.1.3

This interface fixes the concrete actor, representation, coordinates, and
dimension-two plane convention for the remaining model calculations. It
does not assert these calculations. `HexacodeOffenders` transports a proof
of this contract to the recognized source action; its final assembly must
still supply proofs for the even cover and its semilinear extension.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464), and B.4.2(8), printed p.86.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
open ChapterB.QuasisimpleSource

/-- The three remaining model assertions, with the actual pointwise kernels.
The two intended instances are `(evenAction, ⊤)` and `(action, hexSign.ker)`. -/
structure ModelCalculation {H : Type*} [Group H]
    (σ : Representation (ZMod 2) H hexacode) (M : Subgroup H) : Prop where
  generated : offenderSubgroup σ = M
  ratio : quadraticRatio σ = 1
  offenders : ∀ A, IsBestOffender σ A → ∃ P :
      Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier),
    Module.finrank BinaryField.four.Carrier P = 2 ∧
    A = subspaceKernel σ
      ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap) ⊤

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
