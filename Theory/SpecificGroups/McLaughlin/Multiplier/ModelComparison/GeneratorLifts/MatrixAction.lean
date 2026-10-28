module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.RationalMaps
/-!
# Integer certificates for the rational action

Clearing the fixed denominator turns each rational image equation into a
small integer matrix-vector identity. Casting that identity back to the
rational coordinates proves the action of the original linear equivalence.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices
open scoped Matrix BigOperators

theorem rational_scaled_mulVec (M : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℤ) (hd : d ≠ 0) (v w : Fin 24 → ℤ) (h : M *ᵥ v = d • w) :
    ((1 / (d : ℚ)) • M.map (Int.castRingHom ℚ)) *ᵥ (fun i => (v i : ℚ)) =
      fun i => (w i : ℚ) := by
  ext i
  rw [Matrix.smul_mulVec]
  change (1 / (d : ℚ)) * (M.map (Int.castRingHom ℚ) *ᵥ ((Int.castRingHom ℚ) ∘ v)) i = _
  rw [← RingHom.map_mulVec, h]
  change (1 / (d : ℚ)) * ((d * w i : ℤ) : ℚ) = _
  push_cast
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  field_simp

theorem mapA_vector (v w : Fin 24 → ℤ) (h : matrixAData *ᵥ v = (4 : ℤ) • w) :
    mapA (rationalEmbedding (vectorOfData v)) = rationalEmbedding (vectorOfData w) := by
  have hv : rationalEmbedding (vectorOfData v) = reindex (fun i => (v i : ℚ)) := rfl
  have hw : rationalEmbedding (vectorOfData w) = reindex (fun i => (w i : ℚ)) := rfl
  rw [hv, hw]
  change reindex (matrixA *ᵥ reindex.symm (reindex (fun i => (v i : ℚ)))) = _
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg reindex
  simpa only [matrixA, matrixADataQ, Int.cast_ofNat, one_div] using
    rational_scaled_mulVec matrixAData 4 (by decide) v w h

theorem mapB_vector (v w : Fin 24 → ℤ) (h : matrixBData *ᵥ v = (8 : ℤ) • w) :
    mapB (rationalEmbedding (vectorOfData v)) = rationalEmbedding (vectorOfData w) := by
  have hv : rationalEmbedding (vectorOfData v) = reindex (fun i => (v i : ℚ)) := rfl
  have hw : rationalEmbedding (vectorOfData w) = reindex (fun i => (w i : ℚ)) := rfl
  rw [hv, hw]
  change reindex (matrixB *ᵥ reindex.symm (reindex (fun i => (v i : ℚ)))) = _
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg reindex
  simpa only [matrixB, matrixBDataQ, Int.cast_ofNat, one_div] using
    rational_scaled_mulVec matrixBData 8 (by decide) v w h
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
