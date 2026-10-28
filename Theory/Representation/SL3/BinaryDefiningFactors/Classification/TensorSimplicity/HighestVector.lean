module

public import Theory.Representation.SL3.BinaryDefiningFactors

/-!
# Highest vectors in the concrete SL₃ tensor words

The four seeds are 1, the first coordinate vector, the last coordinate
functional, and the trace-zero matrix unit E₀₂. Their recursive tensor product
lies on the actual word carrier. A tensor coefficient functional evaluates to
one, proving that this vector is nonzero for every word.

These shared definitions support separate orbit-span and upper-fixed-space
proofs. Neither property is assumed to follow merely from this construction.
Source: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixGroups TensorProduct
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity
variable (K : Type*) [Field K]

/-- Highest vectors 1, e₀, e₂* and the matrix unit E₀₂ in the four factors. -/
def factorSeed : (a : Factor) → Space K a
  | .trivial => (1 : K)
  | .natural => Pi.single 0 1
  | .dual => LinearMap.proj 2
  | .adjoint => ⟨(LinearMap.proj (2 : Fin 3)).smulRight (Pi.single 0 1), by
      simp [LinearMap.trace_smulRight]⟩

private def factorCoefficient : (a : Factor) → Space K a →ₗ[K] K
  | .trivial => LinearMap.id
  | .natural => LinearMap.proj 0
  | .dual =>
      { toFun := fun (f : Module.Dual K (Fin 3 → K)) => f (Pi.single 2 1)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  | .adjoint =>
      { toFun := fun (f : AdjointSpace K) => f.val (Pi.single 2 1) 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

private theorem factorCoefficient_seed (a : Factor) : factorCoefficient K a (factorSeed K a) = 1 := by
  cases a with
  | trivial => rfl
  | natural => change (Pi.single 0 (1 : K) : Fin 3 → K) 0 = 1; simp
  | dual => change (Pi.single 2 (1 : K) : Fin 3 → K) 2 = 1; simp
  | adjoint => simp [factorCoefficient, factorSeed]

/-- The tensor of the highest vectors, on the actual recursive word carrier. -/
def wordSeed : (w : List Factor) → WordSpace K w
  | [] => (1 : K)
  | a :: w => factorSeed K a ⊗ₜ[K] wordSeed w

private def wordCoefficient : (w : List Factor) → WordSpace K w →ₗ[K] K
  | [] => LinearMap.id
  | a :: w => (_root_.TensorProduct.lid K K).toLinearMap ∘ₗ
      _root_.TensorProduct.map (factorCoefficient K a) (wordCoefficient w)

private theorem wordCoefficient_seed (w : List Factor) : wordCoefficient K w (wordSeed K w) = 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (_root_.TensorProduct.lid K K)
      (_root_.TensorProduct.map (factorCoefficient K a) (wordCoefficient K w)
        (factorSeed K a ⊗ₜ[K] wordSeed K w)) = 1
    rw [_root_.TensorProduct.map_tmul, factorCoefficient_seed, ih, _root_.TensorProduct.lid_tmul]
    simp

/-- The tensor highest vector is nonzero, as witnessed by a coefficient functional. -/
theorem wordSeed_ne_zero (w : List Factor) : wordSeed K w ≠ 0 := by
  intro h
  have hh := wordCoefficient_seed K w
  rw [h, map_zero] at hh
  exact zero_ne_one hh

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity
