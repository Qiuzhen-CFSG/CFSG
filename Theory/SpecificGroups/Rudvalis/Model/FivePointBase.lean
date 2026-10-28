module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level5

/-!
# Five points determine an element of the Rudvalis model

Every element of the actual ATLAS-generated group preserves the certified
orbital relation. Its refinement after fixing points 0 through 4 separates
all 4060 points. Thus two model elements agreeing on those five points are
equal: apply orbital rigidity to their quotient.

This reduces verification of word identities to five point comparisons.
It applies to elements of `Model`, not to arbitrary permutations.

Source: the degree-4060 ATLAS action, with attribution and action convention
in `Model.PermutationData`; the checked refinement is in
`OuterNormalizer.Rigidity.Level5`.
-/

namespace Rudvalis
open OuterNormalizer OuterNormalizer.RigidityCertificate

/-- An element of the actual model fixing the first five points is trivial. -/
public theorem eq_one_of_fixes_first_five {g : Model}
    (hg : ∀ x : Fin 4060, x.val < 5 → g • x = x) : g = 1 := by
  apply Subtype.ext
  exact fix_five_eq_one g.val
    (model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.property) hg

/-- Equality of model elements can be checked on the five-point base. -/
public theorem eq_of_smul_first_five {g h : Model}
    (he : ∀ i : Fin 5,
      g • (i.castLE (by decide) : Fin 4060) = h • (i.castLE (by decide) : Fin 4060)) :
    g = h := by
  have hf : h⁻¹ * g = 1 := by
    apply eq_one_of_fixes_first_five
    intro x hx
    have he' : g • x = h • x := he ⟨x.val, hx⟩
    rw [mul_smul, he', inv_smul_smul]
  exact (inv_mul_eq_one.mp hf).symm

end Rudvalis
