module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedCoordinates
/-!
# Semilinear coordinates for normalized mixed SL₃(4) extensions

Central normalization makes each cross block intertwine the natural and dual
central scalars. Since these scalars are ω and ω², the block is semilinear for
Frobenius, and its three coordinate-vector values determine it. The resulting
matrix cocycle has squared inverse transpose on the right.

This is the coordinate input to the mixed-extension upper bound associated
with James (1973), Lemma 8.3 and Aschbacher–Smith H.12.1, printed pp.393–394.
-/

@[expose] public noncomputable section

open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion
open SL3FourNaturalDual ExtensionCoordinates

/-- The dual central scalar acts by the square of the natural central scalar. -/
lemma central_dual (v : W) : constituent .dual z v = (omega^2) • v := by
  change natural (Matrix.SpecialLinearGroup.inverseTranspose z) v = _
  rw [central_inverseTranspose, pow_two, map_mul]
  change natural z (natural z v) = _
  rw [centralScalar_natural, centralScalar_natural, smul_smul, pow_two]

/-- A normalized mixed block is Frobenius-semilinear over the ordinary F₄. -/
lemma normalized_semilinear (c : BlockCocycle .natural .dual) (hc : c.value z = 0)
    (g : SL) (r : F) (v : W) : c.value g (r • v) = r^2 • c.value g v := by
  have h := LinearMap.congr_fun (c.normalized_intertwines hc g) v
  change natural z (c.value g v) = c.value g (constituent .dual z v) at h
  rw [centralScalar_natural, central_dual] at h
  have he : ∀ r : F, r = 0 ∨ r = 1 ∨ r = omega^2 ∨ r = 1 + omega^2 := by decide +kernel
  rcases he r with rfl | rfl | rfl | rfl
  · simp
  · simp
  · rw [← h, ← pow_mul, SL2FourNatural.pow_four]
  · rw [add_smul, one_smul, map_add, ← h]
    have he : (1 + omega^2)^2 = 1 + omega := by decide +kernel
    rw [he, add_smul, one_smul]

/-- Matrix coefficients of the normalized cross block on the coordinate vectors. -/
def coeff (c : BlockCocycle .natural .dual) (g : SL) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => c.value g (Pi.single j 1) i

/-- These coefficients reconstruct the entire binary map. -/
lemma coeff_apply (c : BlockCocycle .natural .dual) (hc : c.value z = 0)
    (g : SL) (v : W) : c.value g v = (coeff c g).mulVec (squareVector v) := by
  have he : v = ∑ j : Fin 3, v j • (Pi.single j (1 : F) : W) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]
  rw [he, map_sum]
  simp only [normalized_semilinear c hc]
  funext i
  simp only [Matrix.mulVec, dotProduct, squareVector_apply, coeff]
  rw [← he]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The right matrix in the mixed cocycle law: squared inverse transpose. -/
def right (g : SL) : Matrix (Fin 3) (Fin 3) F :=
  (Matrix.SpecialLinearGroup.inverseTranspose g).val.map SL2FourNatural.fieldFrobenius

/-- Squared inverse transpose is multiplicative. -/
lemma right_mul (g h : SL) : right (g * h) = right g * right h := by
  simp only [right, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

/-- The coefficient matrix vanishes at the identity. -/
lemma coeff_one (c : BlockCocycle .natural .dual) : coeff c 1 = 0 := by
  apply Matrix.ext
  intro i j
  simp [coeff, c.one]

/-- The exact matrix cocycle law, with the Frobenius twist on the right. -/
lemma coeff_mul (c : BlockCocycle .natural .dual) (hc : c.value z = 0)
    (g h : SL) : coeff c (g * h) = g.val * coeff c h + coeff c g * right h := by
  apply Matrix.ext
  intro i j
  have he := congrFun (LinearMap.congr_fun (c.mul g h) (Pi.single j 1)) i
  change c.value (g * h) (Pi.single j 1) i =
    (g.val.mulVec (c.value h (Pi.single j 1))) i +
    c.value g ((Matrix.SpecialLinearGroup.inverseTranspose h).val.mulVec (Pi.single j 1)) i at he
  rw [coeff_apply c hc g] at he
  simpa only [coeff, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    squareVector_apply, Matrix.mulVec_single_one, right, Matrix.map_apply,
    Matrix.add_apply, Matrix.col_apply,
    SL2FourNatural.fieldFrobenius_apply] using he

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion
