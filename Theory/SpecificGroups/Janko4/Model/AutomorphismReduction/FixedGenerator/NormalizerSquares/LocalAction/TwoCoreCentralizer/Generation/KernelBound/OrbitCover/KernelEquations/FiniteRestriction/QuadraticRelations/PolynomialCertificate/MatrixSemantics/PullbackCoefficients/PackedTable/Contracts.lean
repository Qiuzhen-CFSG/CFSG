module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.Fast

/-!
# Finite witness contracts for the packed table

The source-column test compares individual Boolean entries with the unchanged
125 matrices. The image test checks multiplication by the candidate form rows.
The output tests compare contracted tensors and whole polarized row segments
with the published data. All are unconditional finite arithmetic obligations.

Their semantic assembly below uses no assertion identifying candidate forms
with the actual exterior forms; that independent calibration remains upstream
of the parent matrix-coefficient assembly. Source: `../../../source/README.md`.
-/

@[expose] public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable

def ColumnCheck (a : Fin 125) : Prop := ∀ i j : Fin 50,
  ((columns.get j).get i).testBit a.val =
    ((restrictionLinearRows.get a).get i).testBit j.val

instance (a : Fin 125) : Decidable (ColumnCheck a) :=
  inferInstanceAs (Decidable (∀ _i _j : Fin 50, _))

def ImageCheck (t : Fin 10) : Prop :=
  images.get t = formColumns (testFormRows t) columns

instance (t : Fin 10) : Decidable (ImageCheck t) :=
  inferInstanceAs (Decidable (_ = _))

def ContractionCheck (e : Fin 987) : Prop :=
  contract (tests.get e).2 (rawBlockFast columns (images.get (tests.get e).1) false) =
      ordered.get e ∧
    contract (tests.get e).2 (rawBlockFast columns (images.get (tests.get e).1) true) =
      reversed.get e

instance (e : Fin 987) : Decidable (ContractionCheck e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def PolarizationCheck (e : Fin 987) : Prop :=
  ∀ a : Fin 125, RowCheck (equationRows.get e) (ordered.get e) (reversed.get e) a

instance (e : Fin 987) : Decidable (PolarizationCheck e) :=
  inferInstanceAs (Decidable (∀ _a : Fin 125, _))

theorem coefficientBasis_of_check (a : Fin 125) (h : ColumnCheck a) :
    coefficientBasis columns a = decodeRestrictionRows (restrictionLinearRows.get a) := by
  funext i j
  exact congrArg (fun b : Bool => if b then (1 : ZMod 2) else 0) (h i j)

/-- Ordered witnesses acquire their matrix meaning after the independent input
and contraction checks. No identification with actual test forms is needed. -/
theorem ordered_coefficients_of_checks
    (hC : ∀ a : Fin 125, ColumnCheck a) (hD : ∀ t : Fin 10, ImageCheck t)
    (hc : ∀ e : Fin 987, ContractionCheck e)
    (e : Fin 987) (a b : Fin 125) :
    bit (ordered.get e) (125*a.val+b.val) =
      bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
        (restrictionLinearRows.get a) (restrictionLinearRows.get b)) 0 ∧
    bit (reversed.get e) (125*a.val+b.val) =
      bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
        (restrictionLinearRows.get b) (restrictionLinearRows.get a)) 0 := by
  have hCa (a : Fin 125) := coefficientBasis_of_check a (hC a)
  have hDa (t : Fin 10) : images.get t = formColumns (testFormRows t) columns := hD t
  constructor
  · rw [← (hc e).1, contract_rawBlockFast, hDa, contract_rawBlock,
      hCa, hCa, pullbackBits_spec]
    rfl
  · rw [← (hc e).2, contract_rawBlockFast, hDa, contract_rawBlock,
      hCa, hCa, pullbackBits_spec]
    rfl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
