module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalModel
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Products

/-!
# Certified matrices for the local J4 three-subgroup

The literal ATLAS program is evaluated using certified packed products.
Inverse rows are identified by multiplying by the actual group inverse, so
no matrix inversion oracle is trusted. The positive words and their 27 normal
forms are then evaluated by multiplication. Source: ATLAS `J4G1-max10W1`,
R. A. Wilson, S. J. Nickerson and J. N. Bray; see `Threes.LocalModel` and
`Model.Data` for the literal program, binary generators, and attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

private theorem mul_matrix {g h : Model} {xs ys zs : Vector Nat 112}
    (hg : toMatrix g = decodeRows xs) (hh : toMatrix h = decodeRows ys)
    (hp : packedMul xs ys = zs) : toMatrix (g * h) = decodeRows zs := by
  rw [map_mul, hg, hh, ← decode_packedMul, hp]

private theorem inv_matrix {g : Model} {xs ys : Vector Nat 112}
    (hg : toMatrix g = decodeRows xs) (hp : packedMul xs ys = packedOne) :
    toMatrix g⁻¹ = decodeRows ys := by
  have h : toMatrix g * decodeRows ys = 1 := by
    rw [hg, ← decode_packedMul, hp, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ys) := by rw [h]
    _ = decodeRows ys := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_ab (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((a hA) * (b hB)) = decodeRows abRows := by
  exact mul_matrix (toMatrix_a hA) (toMatrix_b hB) product_ab

private theorem eval_ba (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((b hB) * (a hA)) = decodeRows baRows := by
  exact mul_matrix (toMatrix_b hB) (toMatrix_a hA) product_ba

private theorem eval_abPow2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 2) = decodeRows abPow2Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_ab hA hB) (eval_ab hA hB) product_abPow2)

private theorem eval_abPow3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 3) = decodeRows abPow3Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_ab hA hB) (eval_abPow2 hA hB) product_abPow3)

private theorem eval_abCubeB (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((a hA) * (b hB)) ^ 3) * (b hB)) = decodeRows abCubeBRows := by
  exact mul_matrix (eval_abPow3 hA hB) (toMatrix_b hB) product_abCubeB

private theorem eval_abCubeBPow2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((a hA) * (b hB)) ^ 3) * (b hB)) ^ 2) = decodeRows abCubeBPow2Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abCubeB hA hB) (eval_abCubeB hA hB) product_abCubeBPow2)

private theorem eval_abCubeBPow4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((a hA) * (b hB)) ^ 3) * (b hB)) ^ 4) = decodeRows abCubeBPow4Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abCubeBPow2 hA hB) (eval_abCubeBPow2 hA hB) product_abCubeBPow4)

private theorem eval_abPow4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 4) = decodeRows abPow4Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow2 hA hB) (eval_abPow2 hA hB) product_abPow4)

private theorem eval_abPow8 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 8) = decodeRows abPow8Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow4 hA hB) (eval_abPow4 hA hB) product_abPow8)

private theorem eval_abPow16 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 16) = decodeRows abPow16Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow8 hA hB) (eval_abPow8 hA hB) product_abPow16)

private theorem eval_ab16Inv (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((a hA) * (b hB)) ^ 16)⁻¹) = decodeRows ab16InvRows := by
  exact inv_matrix (eval_abPow16 hA hB) product_ab16Inv

private theorem eval_baPow2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 2) = decodeRows baPow2Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_ba hA hB) (eval_ba hA hB) product_baPow2)

private theorem eval_baPow3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 3) = decodeRows baPow3Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_ba hA hB) (eval_baPow2 hA hB) product_baPow3)

private theorem eval_baPow6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 6) = decodeRows baPow6Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_baPow3 hA hB) (eval_baPow3 hA hB) product_baPow6)

private theorem eval_baPow12 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 12) = decodeRows baPow12Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_baPow6 hA hB) (eval_baPow6 hA hB) product_baPow12)

private theorem eval_baPow24 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 24) = decodeRows baPow24Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_baPow12 hA hB) (eval_baPow12 hA hB) product_baPow24)

private theorem eval_conjSecond (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((a hA) * (b hB)) ^ 16)⁻¹) * (((b hB) * (a hA)) ^ 24)) = decodeRows conjSecondRows := by
  exact mul_matrix (eval_ab16Inv hA hB) (eval_baPow24 hA hB) product_conjSecond

private theorem eval_conjSecondInv (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((((a hA) * (b hB)) ^ 16)⁻¹) * (((b hB) * (a hA)) ^ 24))⁻¹) = decodeRows conjSecondInvRows := by
  exact inv_matrix (eval_conjSecond hA hB) product_conjSecondInv

private theorem eval_secondLeft (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((((a hA) * (b hB)) ^ 16)⁻¹) * (((b hB) * (a hA)) ^ 24))⁻¹) * (((((a hA) * (b hB)) ^ 3) * (b hB)) ^ 4)) = decodeRows secondLeftRows := by
  exact mul_matrix (eval_conjSecondInv hA hB) (eval_abCubeBPow4 hA hB) product_secondLeft

private theorem eval_programSnd (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((((((a hA) * (b hB)) ^ 16)⁻¹) * (((b hB) * (a hA)) ^ 24))⁻¹) * (((((a hA) * (b hB)) ^ 3) * (b hB)) ^ 4)) * (((((a hA) * (b hB)) ^ 16)⁻¹) * (((b hB) * (a hA)) ^ 24))) = decodeRows programSndRows := by
  exact mul_matrix (eval_secondLeft hA hB) (eval_conjSecond hA hB) product_programSnd

private theorem eval_baPow4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 4) = decodeRows baPow4Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_baPow2 hA hB) (eval_baPow2 hA hB) product_baPow4)

private theorem eval_baPow8 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((b hB) * (a hA)) ^ 8) = decodeRows baPow8Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_baPow4 hA hB) (eval_baPow4 hA hB) product_baPow8)

private theorem eval_firstMid (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) = decodeRows firstMidRows := by
  exact mul_matrix (eval_ab hA hB) (eval_baPow8 hA hB) product_firstMid

private theorem eval_abPow5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 5) = decodeRows abPow5Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow2 hA hB) (eval_abPow3 hA hB) product_abPow5)

private theorem eval_abPow9 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 9) = decodeRows abPow9Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow4 hA hB) (eval_abPow5 hA hB) product_abPow9)

private theorem eval_abPow18 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((a hA) * (b hB)) ^ 18) = decodeRows abPow18Rows := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using
    (mul_matrix (eval_abPow9 hA hB) (eval_abPow9 hA hB) product_abPow18)

private theorem eval_conjFirst (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) * (((a hA) * (b hB)) ^ 18)) = decodeRows conjFirstRows := by
  exact mul_matrix (eval_firstMid hA hB) (eval_abPow18 hA hB) product_conjFirst

private theorem eval_conjFirstInv (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) * (((a hA) * (b hB)) ^ 18))⁻¹) = decodeRows conjFirstInvRows := by
  exact inv_matrix (eval_conjFirst hA hB) product_conjFirstInv

private theorem eval_firstLeft (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((((((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) * (((a hA) * (b hB)) ^ 18))⁻¹) * (a hA)) = decodeRows firstLeftRows := by
  exact mul_matrix (eval_conjFirstInv hA hB) (toMatrix_a hA) product_firstLeft

private theorem eval_programFst (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (((((((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) * (((a hA) * (b hB)) ^ 18))⁻¹) * (a hA)) * ((((a hA) * (b hB)) * (((b hB) * (a hA)) ^ 8)) * (((a hA) * (b hB)) ^ 18))) = decodeRows programFstRows := by
  exact mul_matrix (eval_firstLeft hA hB) (eval_conjFirst hA hB) product_programFst

theorem program_fst_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (threeLocalProgram (a hA) (b hB)).1 = decodeRows programFstRows := by
  exact eval_programFst hA hB

theorem program_snd_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (threeLocalProgram (a hA) (b hB)).2 = decodeRows programSndRows := by
  exact eval_programSnd hA hB

theorem u_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (threeLocalU hA hB) = decodeRows uRows := by
  rw [← product_u, decode_packedMul,
    ← product_uPrefix7, decode_packedMul,
    ← product_uPrefix6, decode_packedMul,
    ← product_uPrefix5, decode_packedMul,
    ← product_uPrefix4, decode_packedMul,
    ← product_uPrefix3, decode_packedMul,
    ← product_uPrefix2, decode_packedMul]
  simp [threeLocalU, word, program_fst_matrix, program_snd_matrix, mul_assoc]

theorem v_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (threeLocalV hA hB) = decodeRows vRows := by
  rw [← product_v, decode_packedMul,
    ← product_vPrefix11, decode_packedMul,
    ← product_vPrefix10, decode_packedMul,
    ← product_vPrefix9, decode_packedMul,
    ← product_vPrefix8, decode_packedMul,
    ← product_vPrefix7, decode_packedMul,
    ← product_vPrefix6, decode_packedMul,
    ← product_vPrefix5, decode_packedMul,
    ← product_vPrefix4, decode_packedMul,
    ← product_vPrefix3, decode_packedMul,
    ← product_vPrefix2, decode_packedMul]
  simp [threeLocalV, word, program_fst_matrix, program_snd_matrix, mul_assoc]

theorem z_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (threeLocalZ hA hB) = decodeRows zRows := by
  apply mul_matrix (mul_matrix (mul_matrix
    (inv_matrix (u_matrix hA hB) product_uInv)
    (inv_matrix (v_matrix hA hB) product_vInv) product_invUV)
    (u_matrix hA hB) product_commLeft) (v_matrix hA hB) product_z

theorem normalForm_matrix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (t : Fin 3 × Fin 3 × Fin 3) :
    toMatrix (threeLocalNormalForm hA hB t) = decodeRows (normalRows t) := by
  rcases t with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 0 * decodeRows zRows ^ 0 = decodeRows normal000Rows
    rw [← product_normal000, decode_packedMul, ← product_uv00, decode_packedMul]
    simp only [decode_packedOne, pow_zero]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 0 * decodeRows zRows ^ 1 = decodeRows normal001Rows
    rw [← product_normal001, decode_packedMul, ← product_uv00, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 0 * decodeRows zRows ^ 2 = decodeRows normal002Rows
    rw [← product_normal002, decode_packedMul, ← product_uv00, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 1 * decodeRows zRows ^ 0 = decodeRows normal010Rows
    rw [← product_normal010, decode_packedMul, ← product_uv01, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 1 * decodeRows zRows ^ 1 = decodeRows normal011Rows
    rw [← product_normal011, decode_packedMul, ← product_uv01, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 1 * decodeRows zRows ^ 2 = decodeRows normal012Rows
    rw [← product_normal012, decode_packedMul, ← product_uv01, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 2 * decodeRows zRows ^ 0 = decodeRows normal020Rows
    rw [← product_normal020, decode_packedMul, ← product_uv02, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 2 * decodeRows zRows ^ 1 = decodeRows normal021Rows
    rw [← product_normal021, decode_packedMul, ← product_uv02, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 0 * decodeRows vRows ^ 2 * decodeRows zRows ^ 2 = decodeRows normal022Rows
    rw [← product_normal022, decode_packedMul, ← product_uv02, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 0 * decodeRows zRows ^ 0 = decodeRows normal100Rows
    rw [← product_normal100, decode_packedMul, ← product_uv10, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 0 * decodeRows zRows ^ 1 = decodeRows normal101Rows
    rw [← product_normal101, decode_packedMul, ← product_uv10, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 0 * decodeRows zRows ^ 2 = decodeRows normal102Rows
    rw [← product_normal102, decode_packedMul, ← product_uv10, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 1 * decodeRows zRows ^ 0 = decodeRows normal110Rows
    rw [← product_normal110, decode_packedMul, ← product_uv11, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 1 * decodeRows zRows ^ 1 = decodeRows normal111Rows
    rw [← product_normal111, decode_packedMul, ← product_uv11, decode_packedMul]
    simp only [pow_one]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 1 * decodeRows zRows ^ 2 = decodeRows normal112Rows
    rw [← product_normal112, decode_packedMul, ← product_uv11, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 2 * decodeRows zRows ^ 0 = decodeRows normal120Rows
    rw [← product_normal120, decode_packedMul, ← product_uv12, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 2 * decodeRows zRows ^ 1 = decodeRows normal121Rows
    rw [← product_normal121, decode_packedMul, ← product_uv12, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 1 * decodeRows vRows ^ 2 * decodeRows zRows ^ 2 = decodeRows normal122Rows
    rw [← product_normal122, decode_packedMul, ← product_uv12, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 0 * decodeRows zRows ^ 0 = decodeRows normal200Rows
    rw [← product_normal200, decode_packedMul, ← product_uv20, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 0 * decodeRows zRows ^ 1 = decodeRows normal201Rows
    rw [← product_normal201, decode_packedMul, ← product_uv20, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 0 * decodeRows zRows ^ 2 = decodeRows normal202Rows
    rw [← product_normal202, decode_packedMul, ← product_uv20, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 1 * decodeRows zRows ^ 0 = decodeRows normal210Rows
    rw [← product_normal210, decode_packedMul, ← product_uv21, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 1 * decodeRows zRows ^ 1 = decodeRows normal211Rows
    rw [← product_normal211, decode_packedMul, ← product_uv21, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 1 * decodeRows zRows ^ 2 = decodeRows normal212Rows
    rw [← product_normal212, decode_packedMul, ← product_uv21, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 2 * decodeRows zRows ^ 0 = decodeRows normal220Rows
    rw [← product_normal220, decode_packedMul, ← product_uv22, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [decode_packedOne, pow_zero, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 2 * decodeRows zRows ^ 1 = decodeRows normal221Rows
    rw [← product_normal221, decode_packedMul, ← product_uv22, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    simp only [pow_one, pow_two]
  · simp only [threeLocalNormalForm, map_mul, map_pow, u_matrix, v_matrix, z_matrix]
    change decodeRows uRows ^ 2 * decodeRows vRows ^ 2 * decodeRows zRows ^ 2 = decodeRows normal222Rows
    rw [← product_normal222, decode_packedMul, ← product_uv22, decode_packedMul]
    rw [← product_uPow2, decode_packedMul]
    rw [← product_vPow2, decode_packedMul]
    rw [← product_zPow2, decode_packedMul]
    simp only [pow_two]

end Janko4.Simplicity.ThreeLocalCertificates
