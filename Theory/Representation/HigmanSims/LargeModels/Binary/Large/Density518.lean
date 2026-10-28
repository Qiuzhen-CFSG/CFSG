module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Orbit
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.RankOne
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Columns
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Rows

/-!
# Assembly of the degree-518 binary HS density certificates

The final density calculation has three independent branches: a rank-one
operator in the literal generator algebra, a spanning column orbit, and a
spanning row orbit. Kernel-checked certificates establish all three premises,
and the structural criterion gives the unconditional public
`MatrixAlgebraFull 2` conclusion for the literal ATLAS generators.

The rank-one route uses a complementary inverse instead of evaluating the
saved degree-517 polynomial. See `Density518/Projection.lean` for its proof
and `Density518/source/README.md` for the certificate interfaces and reproduction.
Source: R. A. Wilson et al., ATLAS HSG1-f2r518B0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix

/-- The literal rank-one, column-orbit and row-orbit certificates suffice. -/
theorem matrixAlgebraFull_of_rank_one_and_spans
    (hprojector : vecMulVec u v ∈ Q)
    (hcolumns : Submodule.span (ZMod 2)
      (Set.range (fun i => (columnActor i).mulVec u)) = ⊤)
    (hrows : Submodule.span (ZMod 2)
      (Set.range (fun i => vecMul v (rowActor i))) = ⊤) : MatrixAlgebraFull 2 := by
  change Q = ⊤
  exact G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q u v columnActor rowActor columnActor_mem rowActor_mem hprojector hcolumns hrows

/-- The complete numerical contract, with every required identity explicit.
Neither carrier descent nor group-theoretic assumptions enter this calculation. -/
theorem matrixAlgebraFull_of_certificates
    (hsum : D = algebraElement)
    (hnullColumn : D.mulVec u = 0)
    (hnullRow : vecMul v D = 0)
    (hcomplement : (D + vecMulVec u v) * E = 1)
    (hcolumnOrbit : ∀ i, (columnActor i).mulVec u = C.col i)
    (hcolumnInverse : C * Ci = 1)
    (hrowOrbit : ∀ i, vecMul v (rowActor i) = R.row i)
    (hrowInverse : R * Ri = 1) : MatrixAlgebraFull 2 := by
  apply matrixAlgebraFull_of_rank_one_and_spans
  · exact rank_one_mem_of_complement_inverse Q D E u v
      (by rw [hsum]; exact algebraElement_mem) pair_eq_one hnullColumn hnullRow hcomplement
  · exact column_span_of_certificates hcolumnOrbit hcolumnInverse
  · exact row_span_of_certificates hrowOrbit hrowInverse

/-- The two published degree-518 binary HS matrices generate the full matrix
algebra. Every rank-one and orbit certificate is discharged. -/
theorem matrixAlgebraFull : MatrixAlgebraFull 2 :=
  matrixAlgebraFull_of_rank_one_and_spans rank_one_mem column_span row_span

end Representation.HigmanSims.LargeModels.Binary.Large.Density518
