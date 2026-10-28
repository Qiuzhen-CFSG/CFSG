module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.Arithmetic
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R2
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo.R3

/-!
# Certified numerical products for the last two HS relators

The R2 branch consists of gates 34--38, ending at the identity candidate 40.
The R3 branch consists of gates 39--45, ending at the identity candidate 47.
Both branches certify every row of the literal numerical matrices in
`Products`, without an interpretation of any earlier candidate as a word.

The interval split combines the unconditional R2 and R3 certificates into
`last_products`. The other three numerical batches remain with the full
long-word assembly owner. Source:
`LongWords/source/circuit.json`, the theorems `relation_11` and `relation_12`
in `Circuit.lean`, and the unchanged `Descent/source/HSG1-P1.M` (R2 and R3).
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

/-- Combine the two independent numerical branches without dropping either
source relator. This theorem does not supply either numerical premise. -/
theorem last_products_of_r2_r3
    (hr2 : ∀ i : Fin 46, 34 ≤ i.val → i.val < 39 → ProductCheck i)
    (hr3 : ∀ i : Fin 46, 39 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i := by
  intro i hi
  by_cases h : i.val < 39
  · exact hr2 i hi h
  · exact hr3 i (by omega)

/-- All twelve literal products for R2 and R3, including both identity outputs,
with no additional hypotheses. -/
theorem last_products : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i :=
  last_products_of_r2_r3 r2_products r3_products

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
