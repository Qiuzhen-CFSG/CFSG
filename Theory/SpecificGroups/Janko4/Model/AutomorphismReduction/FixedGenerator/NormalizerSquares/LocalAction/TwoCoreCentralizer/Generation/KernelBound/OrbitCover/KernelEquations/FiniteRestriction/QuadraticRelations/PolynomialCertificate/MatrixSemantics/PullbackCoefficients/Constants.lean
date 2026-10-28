module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Arithmetic

/-!
# Constant coefficients of the selected matrix equations

The constant is the upper triangular pairing functional in block zero and is
zero in each exterior block. A kernel check compares the Boolean list of
constant bits with the packed functional evaluator. Its proved interpretation
then gives the statement about the actual restriction pairing.

Source and numerical provenance: the polynomial certificate's `source/README.md`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates PullbackCoefficients

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem constants_map :
    equationRows.toList.map (fun p => p.testBit 0) =
      tests.toList.map (fun t => if t.1.val = 0 then
        (upperBits t.2 restrictionPairingRows).testBit 0 else false) := by
  decide +kernel

/-- The actual constant term of every selected polynomial row. -/
theorem equationRows_constant
    (e : Fin 987) :
    bit (equationRows.get e) 0 =
      if (tests.get e).1.val = 0 then upperValue (tests.get e).2 restrictionPairing else 0 := by
  have h := congrArg (fun v : List Bool => v[e.val]?) constants_map
  simp only [List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem e.isLt, Option.map_some, Option.some.injEq] at h
  change (equationRows.get e).testBit 0 =
    (if (tests.get e).1.val = 0 then
      (upperBits (tests.get e).2 restrictionPairingRows).testBit 0 else false) at h
  have hb := congrArg (fun b : Bool => if b then (1 : ZMod 2) else 0) h
  refine hb.trans ?_
  by_cases he : (tests.get e).1.val = 0
  · simp only [he, if_true]
    exact upperBits_spec _ _
  · simp only [he, if_false, Bool.false_eq_true]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
