module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Descent
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000

/-!
# The two large binary Higman–Sims models

The literal published matrix pairs of degrees 518 and 1000 generate their full
matrix algebras, by checked rank-one operators and spanning row and column
orbits. The checked tensor(20,56) row subquotient and exteriorSquare(56) row
subspace construct marked actions of the literal HS permutation carrier.
Annihilator-quotient descent implements the dual row action with the raw left
matrices. Matrix fullness then proves absolute irreducibility of these actions.

All numerical certificates are discharged. Only the marked degree-twenty
comparison and degree-56 action remain inputs to the constructions; their
producers and the four-model assembly are separate from this large pair.
The degree-1000 construction needs only the degree-56 action.

Source: R. A. Wilson et al., ATLAS HSG1-f2r518B0 and HSG1-f2r1000B0.
Attribution and conventions are in `Binary/source/README.md`; certificate
interfaces and arithmetic measurements are in `Large/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large

/-- The degree-518 matrix fullness contract, with no additional hypotheses. -/
theorem matrixAlgebraFull_two : MatrixAlgebraFull 2 :=
  Density518.matrixAlgebraFull

/-- The degree-1000 matrix fullness contract, with no additional hypotheses. -/
theorem matrixAlgebraFull_three : MatrixAlgebraFull 3 :=
  Density1000.matrixAlgebraFull

/-- Every action with the literal degree-518 generator matrices is absolutely
irreducible, by the unconditional matrix fullness calculation. -/
theorem absolutelyIrreducible_two (C : MarkedAction 2) :
    C.action.IsAbsolutelyIrreducible :=
  C.absolutelyIrreducible matrixAlgebraFull_two

/-- Every action with the literal degree-1000 generator matrices is absolutely
irreducible, by the unconditional matrix fullness calculation. -/
theorem absolutelyIrreducible_three (C : MarkedAction 3) :
    C.action.IsAbsolutelyIrreducible :=
  C.absolutelyIrreducible matrixAlgebraFull_three

/-- The degree-518 marked action from the certified tensor row subquotient. -/
theorem nonempty_markedAction_two
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (C56 : MarkedAction 0) : Nonempty (MarkedAction 2) :=
  Tensor518.markedAction h20 C56

/-- The degree-1000 marked action from the certified exterior-square row subspace. -/
theorem nonempty_markedAction_three (C56 : MarkedAction 0) :
    Nonempty (MarkedAction 3) :=
  Exterior1000.markedAction C56

/-- The constructed degree-518 action is absolutely irreducible. Only the
marked degree-twenty comparison and degree-56 action remain inputs. -/
theorem exists_absolutelyIrreducible_markedAction_two
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (C56 : MarkedAction 0) :
    ∃ C : MarkedAction 2, C.action.IsAbsolutelyIrreducible := by
  obtain ⟨C⟩ := nonempty_markedAction_two h20 C56
  exact ⟨C, C.absolutelyIrreducible matrixAlgebraFull_two⟩

/-- The constructed degree-1000 action is absolutely irreducible. Only the
marked degree-56 action remains an input. -/
theorem exists_absolutelyIrreducible_markedAction_three (C56 : MarkedAction 0) :
    ∃ C : MarkedAction 3, C.action.IsAbsolutelyIrreducible := by
  obtain ⟨C⟩ := nonempty_markedAction_three C56
  exact ⟨C, C.absolutelyIrreducible matrixAlgebraFull_three⟩

end Representation.HigmanSims.LargeModels.Binary.Large
