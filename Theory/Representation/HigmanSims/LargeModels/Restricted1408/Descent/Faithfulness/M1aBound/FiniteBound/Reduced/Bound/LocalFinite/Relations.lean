module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalBase

/-!
# Relations sufficient for the local order bound

These seven words are candidates suggested by the retained permutation image.
Only the two involution words and the product cube are proved here from the
reduced presentation. The other four remain explicit premises: an identity
in the permutation image is not an identity in the abstract reduced carrier.
The checked coset certificate consumes precisely these words. See
`source/README.md` for their provenance and the remaining derivation contract.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite
open Subgroup.CosetWordCertificate

/-- Signed words in the literal local generating family, in its fixed order. -/
def relatorWord (r : Fin 7) : Word (Fin 3) :=
  ![[(1, true), (1, true)],
    [(0, true), (0, true)],
    [(2, true), (2, true), (2, true), (2, true), (2, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(1, true), (2, false), (1, true), (0, true), (2, true), (1, true), (2, false), (1, true), (2, false), (0, true), (2, true), (0, true)],
    [(1, true), (2, false), (2, false), (1, true), (2, true), (1, true), (2, false), (2, false), (1, true), (2, false), (1, true), (2, false)],
    [(2, true), (1, true), (2, true), (1, true), (0, true), (1, true), (2, true), (0, true), (2, true), (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (2, false), (1, true), (0, true), (2, false), (2, false), (1, true), (0, true), (2, true), (2, true), (0, true), (1, true)]] r

/-- The four words not already supplied by the order-six base calculation. -/
def extraIndex : Fin 4 → Fin 7 := ![2, 4, 5, 6]

def extraRelatorWord (r : Fin 4) : Word (Fin 3) := relatorWord (extraIndex r)

theorem relator_zero : eval subgroupGenerator (relatorWord 0) = 1 := by
  change subgroupGenerator 1 * (subgroupGenerator 1 * 1) = 1
  have h : subgroupGenerator 1 ^ 2 = 1 := Subtype.ext third_square
  simpa [pow_two, mul_assoc] using h

theorem relator_one : eval subgroupGenerator (relatorWord 1) = 1 := by
  change subgroupGenerator 0 * (subgroupGenerator 0 * 1) = 1
  have h : subgroupGenerator 0 ^ 2 = 1 := Subtype.ext second_square
  simpa [pow_two, mul_assoc] using h

theorem relator_three : eval subgroupGenerator (relatorWord 3) = 1 := by
  have h : (subgroupGenerator 0 * subgroupGenerator 1) ^ 3 = 1 :=
    Subtype.ext second_third_cube
  simpa [relatorWord, eval_cons, pow_succ, mul_assoc] using h

/-- Exactly the missing four identities suffice for every certificate relator. -/
theorem relators_valid_of_extra
    (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1)
    (r : Fin 7) : eval subgroupGenerator (relatorWord r) = 1 := by
  fin_cases r
  · exact relator_zero
  · exact relator_one
  · exact hr 0
  · exact relator_three
  · exact hr 1
  · exact hr 2
  · exact hr 3

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite
