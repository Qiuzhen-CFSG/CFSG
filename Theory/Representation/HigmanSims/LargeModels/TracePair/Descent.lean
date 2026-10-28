module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixCertificate
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.PermutationRelations
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Marked

/-!
# Factoring the degree-896 matrices through the literal HS carrier

The free-group evaluation onto the permutation carrier is surjective. A proof
that its kernel follows from the retained ATLAS relators, together with checked
matrix relators, therefore gives a representation of that exact carrier. The
matrix-to-linear-map algebra equivalence supplies the raw column action and
preserves its two required markings.

The final two theorems apply this constructed action to the actual product
element and to the density criterion for absolute irreducibility. Presentation
completeness and the finite matrix checks remain explicit inputs here; this
conditional construction does not assert `markedAction_exists`.

Source: ATLAS HSG1-p100B0, HSG1-f4r896aB0 and HSG1-P1.M. See the retained
sources in `TracePair/source/` and `Descent/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair
open Sporadic.LeechRelated.HS
open Descent

/-- Actual representation obtained by factoring through the carrier evaluation.
Its matrices act directly on columns; no inverse transpose is used. -/
noncomputable def representationOfRelators (hp : RelatorsPresentCarrier)
    (C : MatrixRelatorCertificate) : Representation Four Carrier (Fin 896 → Four) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp <|
    (Units.coeHom _).comp (descend hp C.a C.b C.relations)

/-- The kernel and matrix certificates construct the required marked action. -/
noncomputable def markedActionOfRelators (hp : RelatorsPresentCarrier)
    (C : MatrixRelatorCertificate) : MarkedAction where
  rep := representationOfRelators hp C
  matrix_a := by
    change LinearMap.toMatrix' (Matrix.toLinAlgEquiv'
      (↑(descend hp C.a C.b C.relations generatorAElement))) = matrixA
    rw [descend_a, C.matrix_a]
    exact LinearMap.toMatrix'_toLin' _
  matrix_b := by
    change LinearMap.toMatrix' (Matrix.toLinAlgEquiv'
      (↑(descend hp C.a C.b C.relations generatorBElement))) = matrixB
    rw [descend_b, C.matrix_b]
    exact LinearMap.toMatrix'_toLin' _

/-- Conditional existence, awaiting both independent certificates. -/
theorem markedAction_exists_of_relators (hp : RelatorsPresentCarrier)
    (hC : Nonempty MatrixRelatorCertificate) : Nonempty MarkedAction := by
  obtain ⟨C⟩ := hC
  exact ⟨markedActionOfRelators hp C⟩

/-- The action constructed by descent has the trace at the literal carrier word. -/
theorem representationOfRelators_trace_product (hp : RelatorsPresentCarrier)
    (C : MatrixRelatorCertificate) :
    LinearMap.trace Four _ (representationOfRelators hp C traceElement) =
      (matrixA * matrixB).trace :=
  (markedActionOfRelators hp C).trace_product

/-- Apply the independent density certificate to the descended representation. -/
theorem representationOfRelators_absolutelyIrreducible (hp : RelatorsPresentCarrier)
    (C : MatrixRelatorCertificate) (hfull : MatrixAlgebraFull) :
    (representationOfRelators hp C).IsAbsolutelyIrreducible :=
  (markedActionOfRelators hp C).absolutelyIrreducible hfull

end Representation.HigmanSims.LargeModels.TracePair
