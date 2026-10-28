module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Data
public import Theory.Representation.HigmanSims.LargeModels.Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover

/-!
# Marking and density for the first degree-896 HS model

The two independent finite obligations are descent of the literal matrices to
the permutation-generated HS carrier and generation of the full matrix algebra.
The latter implies absolute irreducibility of every action with this marking,
by density and scalar extension. A matrix trace calculation for AB then gives
the trace of the actual carrier element `generatorAElement * generatorBElement`.

The permutations defining the carrier are inverses of the source right-action
permutations. The published matrices, acting on columns, have the same abstract
word multiplication as this carrier. Geometrically they act on the dual of a
right module. Descent must prove these exact generator equations; presentation
relations by themselves do not supply an action of this carrier.

Source: ATLAS HSG1-p100B0 and HSG1-f4r896aB0; see `TracePair/source/`.
-/

@[expose] public section
open scoped TensorProduct
namespace Representation.HigmanSims.LargeModels.TracePair
open Sporadic.LeechRelated.HS

/-- An actual action of the literal HS carrier with the published marking.
Existence is a separate descent theorem, not part of this definition. -/
structure MarkedAction where
  rep : Representation Four Carrier (Fin 896 → Four)
  matrix_a : LinearMap.toMatrix' (rep generatorAElement) = matrixA
  matrix_b : LinearMap.toMatrix' (rep generatorBElement) = matrixB

/-- The finite matrix-algebra calculation, independent of carrier descent. -/
def MatrixAlgebraFull : Prop :=
  Algebra.adjoin Four ({matrixA, matrixB} : Set (Matrix (Fin 896) (Fin 896) Four)) = ⊤

/-- The matrix calculation gives density for an actual marked action. -/
theorem MarkedAction.dense (M : MarkedAction) (hfull : MatrixAlgebraFull) :
    Algebra.adjoin Four (Set.range M.rep) = ⊤ := by
  let S := Algebra.adjoin Four (Set.range M.rep)
  let e := LinearMap.toMatrixAlgEquiv' (R := Four) (n := Fin 896)
  have htop : S.map e.toAlgHom = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨M.rep generatorAElement, Algebra.subset_adjoin ⟨_, rfl⟩, M.matrix_a⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨M.rep generatorBElement, Algebra.subset_adjoin ⟨_, rfl⟩, M.matrix_b⟩
  apply top_unique
  intro f _
  have hf : e f ∈ S.map e.toAlgHom := by rw [htop]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

/-- Full matrix algebra proves absolute, rather than only base-field,
irreducibility of the marked HS action. -/
theorem MarkedAction.absolutelyIrreducible (M : MarkedAction)
    (hfull : MatrixAlgebraFull) : M.rep.IsAbsolutelyIrreducible := by
  let : Nontrivial (AlgebraicClosure Four ⊗[Four] (Fin 896 → Four)) := by
    rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]
    infer_instance
  constructor
  exact irreducible_of_jacobson_density_surjective _
    ((extendScalars_surj_iff (AlgebraicClosure Four) M.rep).mp (M.dense hfull))

/-- The trace witness is an element of the original permutation carrier. -/
def traceElement : Carrier := generatorAElement * generatorBElement

theorem MarkedAction.trace_product (M : MarkedAction) :
    LinearMap.trace Four _ (M.rep traceElement) = (matrixA * matrixB).trace := by
  rw [LinearMap.trace_eq_matrix_trace Four (Pi.basisFun Four (Fin 896))]
  change (LinearMap.toMatrix' (M.rep traceElement)).trace = _
  rw [traceElement, map_mul, LinearMap.toMatrix'_mul, M.matrix_a, M.matrix_b]

end Representation.HigmanSims.LargeModels.TracePair
