module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
/-!
# The actual diagonal Cartan action on the central root plane

Diagonal matrix multiplication defines the torus homomorphism. Direct matrix
multiplication gives weights a² and ab on roots 0 and 4. The established Borel
normalizer theorem supplies normalization of the actual unipotent subgroup.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202.
-/

@[expose] public section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F]

noncomputable def diagonalTorusHom : (Fˣ × Fˣ) →* Sp F where
  toFun x := diagonalTorus x.1 x.2
  map_one' := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [diagonalTorus, Matrix.diagonal]
  map_mul' x y := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [mul_comm]

theorem diagonalTorusHom_apply (a : Fˣ × Fˣ) :
    diagonalTorusHom a = diagonalTorus a.1 a.2 := rfl

theorem diagonalTorus_normalizes (a : Fˣ × Fˣ) :
    diagonalTorusHom a ∈ normalizer (unipotent (F := F) : Set (Sp F)) := by
  rw [← borel_eq_normalizer_unipotent]
  exact diagonalTorus_mem_borel _ _

variable [CharP F 2]
theorem diagonalTorus_weights (a : Fˣ × Fˣ) (s t : F) :
    diagonalTorusHom a * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
        (diagonalTorusHom a)⁻¹ =
      parameter (Multiplicative.ofAdd ((a.1 : F)^2*s),
        Multiplicative.ofAdd ((a.1 : F)*(a.2 : F)*t)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change (diagonalTorus a.1 a.2).val * (theta s t).val.val =
    (theta _ _).val.val * (diagonalTorus a.1 a.2).val
  rw [theta, theta, element_matrix, element_matrix]
  simp only [diagonalTorus]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, pow_two, mul_assoc, mul_comm]
  left
  rw [mul_left_comm, mul_inv_cancel₀ a.1.ne_zero, mul_one]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
