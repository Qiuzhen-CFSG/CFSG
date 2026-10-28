module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Data

/-!
# Checked inverse-transversal corrections for native M23

Each saved representative is a certified word in the native generators.
Their images of point 9 enumerate all 23 points, and the two block
permutations and point-stabilizer corrections are checked on actual
permutations. The final identity is exactly the one used by coinduction.

Source application: Guralnick--Malle I, Proposition 5.1, M23 paragraph;
original candidate in `InducedHeads/source/native-candidate.json`.
-/

open Sporadic.Mathieu Sporadic.Mathieu.LargeInvolutionGeneration
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
@[expose] public noncomputable section

theorem transversal_apply (i : Fin 23) (x : Fin 23) :
    (transversal i).val x = transversalPoint i x := by
  rw [transversal, evalWord_apply _ _ letter_apply]
  revert i x
  decide +kernel

theorem transversal_inverse_apply (i : Fin 23) (x : Fin 23) :
    (transversal i).val.symm x = transversalInversePoint i x := by
  apply (transversal i).val.injective
  rw [_root_.Equiv.apply_symm_apply, transversal_apply]
  revert i x
  decide +kernel

def blockPerm (k : Fin 2) : _root_.Equiv.Perm (Fin 23) where
  toFun := destination k
  invFun := sourceBlock k
  left_inv := by revert k; decide +kernel
  right_inv := by revert k; decide +kernel

def orbitPoint : Fin 23 → Fin 23 := fun i => transversalPoint i 9

theorem orbitPoint_bijective : Function.Bijective orbitPoint := by decide +kernel

theorem correction_fixes (k : Fin 2) (i : Fin 23) :
    (transversal (blockPerm k i))⁻¹ * actor k * transversal i ∈ Models.pointGroup := by
  change (transversal (blockPerm k i)).val.symm
    ((actor k).val ((transversal i).val 9)) = 9
  rw [transversal_apply, generator_apply, transversal_inverse_apply]
  revert k i
  decide +kernel

/-- In Lean multiplication this is t_j⁻¹ g t_i, the reversal of GAP's t_i g t_j⁻¹. -/
def correction (k : Fin 2) (i : Fin 23) : Models.pointGroup :=
  ⟨(transversal (blockPerm k i))⁻¹ * actor k * transversal i, correction_fixes k i⟩

def correctionPoint (k : Fin 2) (i x : Fin 23) : Fin 23 :=
  transversalInversePoint (blockPerm k i) (generatorPoint k (transversalPoint i x))

theorem correction_apply (k : Fin 2) (i x : Fin 23) :
    (correction k i).val.val x = correctionPoint k i x := by
  change (transversal (blockPerm k i)).val.symm
    ((actor k).val ((transversal i).val x)) = _
  rw [transversal_apply, generator_apply, transversal_inverse_apply]
  rfl

/-- Exact inverse-transversal identity used by coinduced evaluation. -/
theorem correction_mul_inverse (k : Fin 2) (i : Fin 23) :
    (correction k i).val * (transversal i)⁻¹ =
      (transversal (blockPerm k i))⁻¹ * actor k := by
  change ((transversal (blockPerm k i))⁻¹ * actor k * transversal i) *
    (transversal i)⁻¹ = _
  group

end
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
