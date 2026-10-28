module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Assembly
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large
public import Theory.Representation.HigmanSims.Twenty.Comparison
import Mathlib.Tactic.FinCases

/-!
# Binary Higman--Sims models

The certified degree-twenty permutation comparison supplies the marked actions
of degrees 56 and 132 through exterior-square row sections. The degree-56
action then supplies degree 518 through tensor(20,56) and degree 1000 through
exterior-square(56). These constructions act on the literal permutation-generated
HS carrier, preserving its inverted source generators and the raw left matrices.

The four proved matrix-fullness certificates give absolute irreducibility.
Thus every premise of `binaryModelsExist` is discharged, and scalar extension
gives the four irreducible models over every characteristic-two field. The
construction itself needs no simplicity assumption; the existence contract
retains the source-inherited simplicity hypothesis.

Source: the four ATLAS binary HS candidates; see `Binary/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels

open Sporadic.LeechRelated.HS

namespace Binary

/-- All four marked actions on the literal HS carrier, with every comparison
and numerical certificate supplied by its construction. -/
theorem nonempty_markedAction (i : Fin 4) : Nonempty (MarkedAction i) := by
  have h20 := Twenty.Comparison.nonempty_markedComparison
  obtain ⟨C56⟩ := Small.nonempty_markedAction_zero_of_twenty h20
  fin_cases i
  · exact ⟨C56⟩
  · exact Small.nonempty_markedAction_one_of_twenty h20
  · exact Large.nonempty_markedAction_two h20 C56
  · exact Large.nonempty_markedAction_three C56

/-- Each literal binary generator pair generates its full matrix algebra. -/
theorem matrixAlgebraFull (i : Fin 4) : MatrixAlgebraFull i := by
  fin_cases i
  · exact Small.matrixAlgebraFull_zero
  · exact Small.matrixAlgebraFull_one
  · exact Large.matrixAlgebraFull_two
  · exact Large.matrixAlgebraFull_three

end Binary

/-- The four absolutely irreducible binary HS models of degrees 56, 132,
518 and 1000, with no additional construction premises. -/
theorem binaryModelsExist : BinaryModelsExist :=
  Binary.binaryModelsExist_of_marked_actions (fun _ => Binary.nonempty_markedAction)
    Binary.matrixAlgebraFull

/-- The constructed binary models supply the four required degrees over any
characteristic-two coefficient field. -/
theorem binaryModels_over_field_constructed (hs : IsSimpleGroup Carrier)
    (F : Type*) [Field F] [CharP F 2] :
    ∃ ρ : ∀ i, Representation F Carrier (Fin (binaryDegree i) → F),
      ∀ i, (ρ i).IsIrreducible :=
  binaryModels_over_field binaryModelsExist hs F

end Representation.HigmanSims.LargeModels
