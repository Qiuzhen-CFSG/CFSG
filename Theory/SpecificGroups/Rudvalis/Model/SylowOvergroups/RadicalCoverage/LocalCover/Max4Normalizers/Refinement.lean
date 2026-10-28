module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.ImageSets
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Refinement

/-!
# Refinement with the marked 28-point set

Count neighbors in an invariant color cell in the certified Rudvalis orbital.
The finite rows, cells, and counts are checked by the kernel. These calculations
use the preserved ATLAS action (see `Model.PermutationData`), GLS3 Table 5.3r.
Witness generation: `Max4Normalizers/source/GenerateRefinement.py`.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.RefinementCertificate

open Rudvalis.OuterNormalizer Rudvalis.OuterNormalizer.RigidityCertificate
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def initialColor (k : Nat) (x : Fin 4060) : Nat :=
  if x.val < k then x.val else if x ∈ pointSet then k else k + 1

public theorem model_relation (g : Model) : g.val ∈ relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.property

public theorem initialColor_preserved (k : Nat) (g : Model)
    (hg : g ∈ pointSetStabilizer)
    (hf : ∀ x : Fin 4060, x.val < k → g • x = x) :
    ∀ x, initialColor k (g • x) = initialColor k x := by
  intro x
  by_cases hx : x.val < k
  · rw [hf x hx]
  · have hy : ¬ (g • x).val < k := by
      intro hy
      have he := MulAction.injective g (hf (g • x) hy)
      exact hx (he ▸ hy)
    simp only [initialColor, if_neg hx, if_neg hy,
      (mem_pointSetStabilizer g).mp hg x]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.RefinementCertificate
