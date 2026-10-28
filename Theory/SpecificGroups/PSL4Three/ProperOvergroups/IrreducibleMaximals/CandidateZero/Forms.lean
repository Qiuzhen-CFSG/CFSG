module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Data

/-!
# The four-form action of the first PSL₄(3) candidate

The four explicit generators permute a family consisting of two alternating
forms and their negatives. Pullback reverses multiplication, so the permutation
attached to a matrix is the inverse of its pullback permutation. This gives an
actual homomorphism from the generated matrix subgroup to S₄. Its kernel fixes
the first form, the standard nondegenerate symplectic form, exactly.

All generator identities are checked by kernel reduction on the explicit
matrices. The form family was found by a finite calculation; no group order,
abstract identification, or subgroup classification is used.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero

public abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] public def formMatrix : Fin 4 → Mat :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 2, 0, 0, 0; 0, 2, 0, 0],
    !![0, 1, 2, 2; 2, 0, 0, 1; 1, 0, 0, 1; 1, 2, 2, 0],
    !![0, 0, 2, 0; 0, 0, 0, 2; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 2, 1, 1; 1, 0, 0, 2; 2, 0, 0, 2; 2, 1, 1, 0]]

private theorem formMatrix_injective : Function.Injective formMatrix := by decide

private def pull (g : SL) (B : Mat) : Mat := (g : Mat)ᵀ * B * (g : Mat)

private theorem pull_one (B : Mat) : pull 1 B = B := by simp [pull]

private theorem pull_mul (g h : SL) (B : Mat) :
    pull (g * h) B = pull h (pull g B) := by
  simp [pull, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem pull_injective (g : SL) : Function.Injective (pull g) := by
  intro B C h
  have := congrArg (pull g⁻¹) h
  simpa only [← pull_mul, mul_inv_cancel, pull_one] using this

private def familyStabilizer : Subgroup SL where
  carrier := {g | ∃ σ : Equiv.Perm (Fin 4), ∀ i, pull g (formMatrix (σ i)) = formMatrix i}
  one_mem' := ⟨1, fun i => pull_one _⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ * τ, fun i => ?_⟩
    rw [pull_mul]
    change pull h (pull g (formMatrix (σ (τ i)))) = _
    rw [hσ, hτ]
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun i => ?_⟩
    have h := congrArg (pull g⁻¹) (hσ (σ⁻¹ i))
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply, ← pull_mul, mul_inv_cancel, pull_one] using h.symm

private def generatorPerm (j : Fin 4) : Equiv.Perm (Fin 4) :=
  ![1, 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3] j

private theorem generator_certificate (j : Fin 4) (i : Fin 4) :
    pull (candidateGenerator 0 j) (formMatrix (generatorPerm j i)) = formMatrix i := by
  fin_cases j <;> fin_cases i <;> decide

/-- The matrix subgroup whose projective image is the first candidate. -/
@[expose] public def lift : Subgroup SL := Subgroup.closure (Set.range (candidateGenerator 0))

private theorem lift_le_familyStabilizer : lift ≤ familyStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact ⟨generatorPerm j, generator_certificate j⟩

private noncomputable def perm (g : lift) : Equiv.Perm (Fin 4) :=
  (lift_le_familyStabilizer g.property).choose

private theorem perm_spec (g : lift) (i : Fin 4) :
    pull g.val (formMatrix (perm g i)) = formMatrix i :=
  (lift_le_familyStabilizer g.property).choose_spec i

private theorem perm_unique (g : lift) (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ i, pull g.val (formMatrix (σ i)) = formMatrix i) : perm g = σ := by
  apply Equiv.ext
  intro i
  apply formMatrix_injective
  apply pull_injective g.val
  rw [perm_spec, hσ]

/-- The genuine permutation action on four alternating forms. -/
public noncomputable def action : lift →* Equiv.Perm (Fin 4) where
  toFun := perm
  map_one' := perm_unique 1 1 (fun i => pull_one _)
  map_mul' g h := perm_unique (g * h) (perm g * perm h) (fun i => by
    change pull (g.val * h.val) (formMatrix (perm g (perm h i))) = _
    rw [pull_mul, perm_spec, perm_spec])

/-- Every element of the permutation kernel fixes the first form exactly. -/
public theorem action_ker_preserves (g : action.ker) :
    (g.val.val : Mat)ᵀ * formMatrix 0 * (g.val.val : Mat) = formMatrix 0 := by
  have hg : perm g.val = 1 := g.property
  have h := perm_spec g.val 0
  rw [hg] at h
  exact h

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero
