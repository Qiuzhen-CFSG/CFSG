module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ASquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.BFifth
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PositiveWords

/-!
# Power relations of the exact degree-896 HS matrices

Complete row certificates prove A² = I, B⁵ = I, (AB)¹¹ = I and (AB²)¹⁰ = I
for the literal packed matrices. The first two also give the inverse witnesses
used by `ofPositiveRelations`. The four index cases assemble these certificates
into exactly the first four positive words of the retained ATLAS presentation
`Descent/source/HSG1-P1.M`; no invertibility or HS action is assumed.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

/-- The first published generator is its own inverse. -/
theorem packedA_sq : (Packed.eval 896 generatorRowsA) ^ 2 = 1 :=
  PowerChecks.ASquare.square_eq_one

/-- Assemble the power family from A² = I and the other three power identities. -/
theorem power_relations_of_remaining
    (hB : (Packed.eval 896 generatorRowsB) ^ 5 = 1)
    (hAB : (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB) ^ 11 = 1)
    (hABB : (Packed.eval 896 generatorRowsA * (Packed.eval 896 generatorRowsB) ^ 2) ^ 10 = 1) :
    ∀ i : Fin 13, i.val < 4 → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  intro i hi
  have h : i = (0 : Fin 13) ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact packedA_sq
  · exact hB
  · exact hAB
  · exact hABB

/-- The first four source relators hold for the exact packed degree-896 matrices. -/
theorem power_relations :
    ∀ i : Fin 13, i.val < 4 → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  power_relations_of_remaining PowerChecks.BFifth.pow_five_eq_one
    PowerChecks.ABPower.pow_eleven_eq_one PowerChecks.ABBPower.pow_ten_eq_one

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
