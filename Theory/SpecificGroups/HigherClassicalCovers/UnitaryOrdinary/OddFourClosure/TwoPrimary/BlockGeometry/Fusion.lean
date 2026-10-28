module

public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Fusion of the two plane-swap reflections in SU₄

The plane sign `diag(-1,-1,1,1)` is conjugate, inside the actual special
unitary group, to every norm-one weighted swap of the two coordinate planes.
Choose a scalar t of norm 1/2. On coordinates (0,2) use the matrix with
columns `(t,-a*t)` and `(a⁻¹*conj(t),conj(t))`; use a = 1 on (1,3).
Each two-dimensional change of basis has determinant one. Their product
is therefore a special unitary conjugator, without any determinant correction
or square-root assumption on a.

The cases a = 1 and a a generator of the norm-one units give the two
reflection fusions used by the block-pair splitting argument. This is the
local geometry supporting Aschbacher--Smith I.1.4(3), printed p.408 of
`refs/quasithin.pdf`, and the unitary multiplier entry in GLS3 §6.1.
-/

open Matrix BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry

variable {F : Type*} [Field F]

/-- Minus the identity on the first coordinate plane, fixing the second. -/
@[expose] public def planeSign : Matrix (Fin 4) (Fin 4) F :=
  diagonal ![-1, -1, 1, 1]

/-- The marked rotation, contained in the transverse SU₂ on coordinates 0 and 2. -/
@[expose] public def rotationMatrix (a : Fˣ) : Matrix (Fin 4) (Fin 4) F :=
  diagonal ![↑a, 1, ↑a⁻¹, 1]

/-- The plane swap followed by the marked rotation. -/
@[expose] public def weightedSwap (a : Fˣ) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, ↑a⁻¹, 0; 0, 0, 0, 1; ↑a, 0, 0, 0; 0, 1, 0, 0]

/-- This order of multiplication matches `DihedralGroup.sr 1 = sr 0 * r 1`. -/
public theorem weightedSwap_eq_swap_mul_rotation (a : Fˣ) :
    weightedSwap a = weightedSwap 1 * rotationMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightedSwap, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private def fusionMatrix (σ : F ≃+* F) (a : Fˣ) (t : F) :
    Matrix (Fin 4) (Fin 4) F :=
  !![t, 0, ↑a⁻¹ * σ t, 0; 0, t, 0, σ t;
     -(↑a * t), 0, σ t, 0; 0, -t, 0, σ t]

private theorem fusionMatrix_det (σ : F ≃+* F) (a : Fˣ) (t : F)
    (ht : 2 * (t * σ t) = 1) : (fusionMatrix σ a t).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [fusionMatrix, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix, show (Fin.succAbove (2 : Fin 4) (2 : Fin 3)) = 3 from rfl, mul_assoc]
  field_simp
  linear_combination (2 * t * σ t + 1) * ht

private theorem fusionMatrix_unitary (J : HermitianForm 4 F) (a : Fˣ)
    (ha : J.conj (a : F) = (a⁻¹ : Fˣ)) (t : F) (ht : 2 * (t * J.conj t) = 1) :
    J.conjTranspose (fusionMatrix J.conj a t) * fusionMatrix J.conj a t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, fusionMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, map_mul, ha, J.conj_involutive t, mul_assoc, mul_left_comm, mul_comm]
  all_goals linear_combination ht

private theorem fusionMatrix_intertwines (σ : F ≃+* F) (a : Fˣ) (t : F) :
    fusionMatrix σ a t * planeSign = weightedSwap a * fusionMatrix σ a t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fusionMatrix, planeSign, weightedSwap, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem isConj_of_half_norm (J : HermitianForm 4 F) (hJ : J.form = 1)
    (a : Fˣ) (ha : J.conj (a : F) = (a⁻¹ : Fˣ)) (t : F)
    (ht : 2 * (t * J.conj t) = 1) (s r : J.specialSubgroup)
    (hs : s.val.val = planeSign) (hr : r.val.val = weightedSwap a) : IsConj s r := by
  have hdet := fusionMatrix_det J.conj a t ht
  let C : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero (fusionMatrix J.conj a t)
    (by rw [hdet]; exact one_ne_zero)
  have hC : C ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · change J.conjTranspose (fusionMatrix J.conj a t) * J.form *
        fusionMatrix J.conj a t = J.form
      rw [hJ, Matrix.mul_one]
      exact fusionMatrix_unitary J a ha t ht
    · exact Units.ext hdet
  refine isConj_iff.mpr ⟨⟨C, hC⟩, ?_⟩
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change fusionMatrix J.conj a t * s.val.val = r.val.val * fusionMatrix J.conj a t
  rw [hs, hr]
  exact fusionMatrix_intertwines J.conj a t

/-- Both marked plane-swap reflections fuse to the plane sign in SU₄ itself.
The norm-one weight is arbitrary; no Mersenne or covering hypothesis is needed. -/
public theorem isConj_planeSign_weightedSwap [Finite F]
    (J : HermitianForm 4 F) (hJ : J.form = 1) {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q)
    (a : Fˣ) (ha : J.conj (a : F) = (a⁻¹ : Fˣ)) (s r : J.specialSubgroup)
    (hs : s.val.val = planeSign) (hr : r.val.val = weightedSwap a) : IsConj s r := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F q := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hc)
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hd : q ∣ 2 := (CharP.cast_eq_zero_iff F q 2).mp h
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  obtain ⟨t, _, ht⟩ := J.exists_norm_of_prime_frobenius hj hc ((2 : F)⁻¹)
    (by rw [map_inv₀]; exact congrArg Inv.inv (map_natCast J.conj 2)) (inv_ne_zero h2)
  exact isConj_of_half_norm J hJ a ha t (by rw [ht, mul_inv_cancel₀ h2]) s r hs hr

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry
