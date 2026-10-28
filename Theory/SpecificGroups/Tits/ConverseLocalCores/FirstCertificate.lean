module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover

/-!
# Five Sylow conjugates in the first Tits parabolic

Conjugation of s2 by the five powers of s1*r1 gives the Sylow normal forms
with indices 2, 1627, 1934, 1439 and 1024. Each equality is checked at all
1600 points by the kernel. Together with the complete five-coset cover,
these identities place s2 in the normal core of the Sylow subgroup.

Source: the Parrott generators and conventions from Parrott (1972), p.683,
transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`.
The indices are computed witnesses; the pointwise proofs certify them.
-/

namespace Tits.ConverseLocalCores.FirstCertificate
open Subgroup ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers

private def rootConjugateIndex (j : Fin 5) : Fin 2048 :=
  ![2, 1627, 1934, 1439, 1024] j

private theorem root_conjugate (j : Fin 5) :
    firstRotation ^ j.val * atlas1600ParrottAssignment .s2 * (firstRotation ^ j.val)⁻¹ =
      atlas1600SylowTwoNormalForm (rootConjugateIndex j) := by
  apply Subtype.ext
  change firstRotation.val ^ j.val * (atlas1600ParrottAssignment .s2).val *
    (firstRotation.val ^ j.val)⁻¹ = _
  have hr : firstRotation.val = Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm := by
    change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val = _
    simp only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]
  rw [hr, atlas1600ParrottAssignment_val, atlas1600SylowTwoNormalForm_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  revert j
  decide +kernel

/-- Each of the five rotation conjugates of s2 lies in the marked Sylow subgroup. -/
public theorem root_conjugate_mem (j : Fin 5) :
    firstRotation ^ j.val * atlas1600ParrottAssignment .s2 * (firstRotation ^ j.val)⁻¹ ∈ S := by
  rw [root_conjugate]
  exact atlas1600SylowTwoNormalForm_mem _

end Tits.ConverseLocalCores.FirstCertificate
