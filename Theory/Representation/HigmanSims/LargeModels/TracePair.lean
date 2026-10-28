module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Marked
public import Theory.Representation.HigmanSims.LargeModels.TracePair.CoefficientExtension
public import Theory.Representation.HigmanSims.LargeModels.ScalarExtension

/-!
# Frobenius construction of the degree-896 HS pair

A single marked action with full generated matrix algebra and trace ω at AB
supplies the required pair. Apply the characteristic-two Frobenius to all
coefficients. This gives another action of the same literal carrier, preserves
absolute irreducibility, and squares the trace; ω and ω² are unequal.
The existing scalar-extension theorem then gives inequivalent irreducible
actions over every algebraically closed characteristic-two field.

Carrier descent, matrix-algebra fullness and the concrete trace calculation
remain explicit inputs here. These conditional theorems do not assert
`traceSeparatedPairExists`. The retained ATLAS candidates are
HSG1-f4r896aB0 and HSG1-f4r896bB0; provenance is in `TracePair/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels
open Sporadic.LeechRelated.HS
namespace TracePair

noncomputable section

/-- Entrywise Frobenius gives a second action of the original HS carrier. -/
def conjugate (M : MarkedAction) : Representation Four Carrier (Fin 896 → Four) :=
  mapCoefficients (frobenius Four 2) M.rep

theorem conjugate_matrix (M : MarkedAction) (g : Carrier) :
    LinearMap.toMatrix' (conjugate M g) =
      (LinearMap.toMatrix' (M.rep g)).map (fun x => x ^ 2) :=
  mapCoefficients_toMatrix (frobenius Four 2) M.rep g

theorem conjugate_absolutelyIrreducible (M : MarkedAction)
    (hfull : MatrixAlgebraFull) : (conjugate M).IsAbsolutelyIrreducible :=
  isAbsolutelyIrreducible_mapCoefficients (frobenius Four 2) M.rep
    (M.absolutelyIrreducible hfull)

/-- The actual element AB separates the marked action from its conjugate. -/
theorem trace_ne_conjugate (M : MarkedAction)
    (htrace : (matrixA * matrixB).trace = omega) :
    LinearMap.trace Four _ (M.rep traceElement) ≠
      LinearMap.trace Four _ (conjugate M traceElement) := by
  rw [conjugate, mapCoefficients_trace]
  change LinearMap.trace Four _ (M.rep traceElement) ≠
    LinearMap.trace Four _ (M.rep traceElement) ^ 2
  rw [M.trace_product, htrace]
  exact omega_ne_sq

end
end TracePair

open TracePair

/-- Assembly from the independent carrier-descent and finite-matrix proofs. -/
theorem traceSeparatedPairExists_of_certificates
    (hdescent : IsSimpleGroup Carrier → Nonempty MarkedAction)
    (hfull : MatrixAlgebraFull)
    (htrace : (matrixA * matrixB).trace = omega) : TraceSeparatedPairExists := by
  intro hs
  obtain ⟨M⟩ := hdescent hs
  exact ⟨Four, inferInstance, inferInstance, inferInstance, M.rep, conjugate M,
    M.absolutelyIrreducible hfull, conjugate_absolutelyIrreducible M hfull,
    traceElement, trace_ne_conjugate M htrace⟩

/-- Application to the exact scalar-extension consumer for the two equal-degree
slots of the seven-model construction. The finite obligations remain explicit. -/
theorem traceSeparatedPair_over_field_of_certificates
    (hdescent : IsSimpleGroup Carrier → Nonempty MarkedAction)
    (hfull : MatrixAlgebraFull)
    (htrace : (matrixA * matrixB).trace = omega)
    (hs : IsSimpleGroup Carrier) (F : Type*) [Field F] [CharP F 2] [IsAlgClosed F] :
    ∃ ρ₁ ρ₂ : Representation F Carrier (Fin 896 → F),
      ρ₁.IsIrreducible ∧ ρ₂.IsIrreducible ∧ IsEmpty (ρ₁.Equiv ρ₂) :=
  traceSeparatedPair_over_field
    (traceSeparatedPairExists_of_certificates hdescent hfull htrace) hs F

end Representation.HigmanSims.LargeModels
