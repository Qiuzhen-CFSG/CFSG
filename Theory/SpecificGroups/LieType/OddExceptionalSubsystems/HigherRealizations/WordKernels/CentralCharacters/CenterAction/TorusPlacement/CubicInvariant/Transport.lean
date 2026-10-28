module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.Model
public import Mathlib.Data.Matrix.Mul

/-!
# Transporting the explicit cubic through an actual invariant block

An injective linear inclusion intertwining the twelve literal generators also
intertwines every evaluated word, including inverse letters. The normalized
cubic from `Model` then forces any scalar action on that block to have cube one.
The concrete E7/E8 applications in `CubicInvariant` use the inverse character
`u⁻¹`, matching the repository's torus convention.

This is the representation step in GLS3 §2.6.2's common-lattice construction
and the central-character calculation in §§1.12.5–6. No assertion that an
arbitrary commuting matrix belongs to the word image is used.
-/

@[expose] public section
open scoped Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.CubicModel
variable {R : Type*} [CommRing R]

section Transfer
variable {n : Type*} [Fintype n] [DecidableEq n]
  (J : (Fin 27 → R) →ₗ[R] (n → R))
  (v : FreeGroup (Bool × Fin 6 × R) →* (Matrix n n R)ˣ)

/-- Generator intertwining extends to the literal word evaluation and its inverse letters. -/
theorem evaluation_intertwines
    (hJ : ∀ s i t x, (v (FreeGroup.of (s, i, t))).val *ᵥ J x =
      J (curve s i t x))
    (w : FreeGroup (Bool × Fin 6 × R)) (x : Fin 27 → R) :
    (v w).val *ᵥ J x = J (evaluation w x) := by
  induction w using FreeGroup.induction_on generalizing x with
  | C1 => simp
  | of a => exact hJ a.1 a.2.1 a.2.2 x
  | inv_of a ih =>
    have h := ih (evaluation (FreeGroup.of a)⁻¹ x)
    simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    simp only [map_inv]
    calc
      (v (FreeGroup.of a))⁻¹.val *ᵥ J x =
          (v (FreeGroup.of a))⁻¹.val *ᵥ
            ((v (FreeGroup.of a)).val *ᵥ J (evaluation (FreeGroup.of a)⁻¹ x)) :=
        congrArg (fun y => (v (FreeGroup.of a))⁻¹.val *ᵥ y) h.symm
      _ = J (evaluation (FreeGroup.of a)⁻¹ x) := by
        simp [Matrix.mulVec_mulVec, ← Units.val_mul]
  | mul a b ha hb =>
    simp only [map_mul, Units.val_mul, Equiv.Perm.mul_apply]
    rw [← Matrix.mulVec_mulVec, hb, ha]

/-- An injective invariant copy of the explicit cubic module detects scalar cubes. -/
theorem cube_of_intertwining (hinj : Function.Injective J)
    (hJ : ∀ s i t x, (v (FreeGroup.of (s, i, t))).val *ᵥ J x =
      J (curve s i t x))
    (w : FreeGroup (Bool × Fin 6 × R)) (t : R)
    (ht : ∀ x, (v w).val *ᵥ J x = J (t • x)) : t ^ 3 = 1 := by
  apply cube_of_evaluation_scalar w t
  intro x
  apply hinj
  rw [← evaluation_intertwines J v hJ, ht]
end Transfer

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.CubicModel
