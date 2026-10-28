module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Projector
/-!
# The zeroth row of the singular matrix vanishes

Only fifteen small rows of the original ATLAS generators occur when the
published word expression acts on the zeroth coordinate row. Their literal
packed values are checked by the kernel, and the resulting sums cancel over
F₂. The theorem supplies the left-kernel premise of `Projector`.
See `../source/README.md` for the expression and ATLAS attribution.
-/

public section
open Matrix Thompson.BinaryMatrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
private def v (x : Nat) : Fin 1792 → ZMod 2 := fun i => bit x i.val
private theorem v_xor (x y : Nat) : v (x ^^^ y) = v x + v y := by
  ext i
  exact bit_xor x y i.val
private theorem v_pow (i : Fin 1792) : v (2^i.val) = Pi.single i 1 := by
  ext j
  simp [v, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]
private theorem row_a0 : Data1792.first.row 0 = Pi.single (1 : Fin 1792) 1 := by
  have h : Data1792.firstRows[0]! = 2 := by decide +kernel
  change v Data1792.firstRows[0]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_a1 : Data1792.first.row 1 = Pi.single (0 : Fin 1792) 1 := by
  have h : Data1792.firstRows[1]! = 1 := by decide +kernel
  change v Data1792.firstRows[1]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_a2 : Data1792.first.row 2 = Pi.single (4 : Fin 1792) 1 := by
  have h : Data1792.firstRows[2]! = 16 := by decide +kernel
  change v Data1792.firstRows[2]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_a3 : Data1792.first.row 3 = Pi.single (5 : Fin 1792) 1 := by
  have h : Data1792.firstRows[3]! = 32 := by decide +kernel
  change v Data1792.firstRows[3]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_a4 : Data1792.first.row 4 = Pi.single (2 : Fin 1792) 1 := by
  have h : Data1792.firstRows[4]! = 4 := by decide +kernel
  change v Data1792.firstRows[4]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_a6 : Data1792.first.row 6 = Pi.single (8 : Fin 1792) 1 := by
  have h : Data1792.firstRows[6]! = 256 := by decide +kernel
  change v Data1792.firstRows[6]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b0 : Data1792.second.row 0 = Pi.single (2 : Fin 1792) 1 := by
  have h : Data1792.secondRows[0]! = 4 := by decide +kernel
  change v Data1792.secondRows[0]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b1 : Data1792.second.row 1 = Pi.single (3 : Fin 1792) 1 := by
  have h : Data1792.secondRows[1]! = 8 := by decide +kernel
  change v Data1792.secondRows[1]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b2 : Data1792.second.row 2 = Pi.single (1 : Fin 1792) 1 + Pi.single (2 : Fin 1792) 1 + Pi.single (3 : Fin 1792) 1 := by
  have h : Data1792.secondRows[2]! = 14 := by decide +kernel
  change v Data1792.secondRows[2]! = _
  rw [h]
  simp only [← v_pow, ← v_xor]
  rfl
private theorem row_b3 : Data1792.second.row 3 = Pi.single (0 : Fin 1792) 1 + Pi.single (1 : Fin 1792) 1 + Pi.single (2 : Fin 1792) 1 := by
  have h : Data1792.secondRows[3]! = 7 := by decide +kernel
  change v Data1792.secondRows[3]! = _
  rw [h]
  simp only [← v_pow, ← v_xor]
  rfl
private theorem row_b4 : Data1792.second.row 4 = Pi.single (6 : Fin 1792) 1 := by
  have h : Data1792.secondRows[4]! = 64 := by decide +kernel
  change v Data1792.secondRows[4]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b5 : Data1792.second.row 5 = Pi.single (7 : Fin 1792) 1 := by
  have h : Data1792.secondRows[5]! = 128 := by decide +kernel
  change v Data1792.secondRows[5]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b6 : Data1792.second.row 6 = Pi.single (4 : Fin 1792) 1 + Pi.single (6 : Fin 1792) 1 := by
  have h : Data1792.secondRows[6]! = 80 := by decide +kernel
  change v Data1792.secondRows[6]! = _
  rw [h]
  simp only [← v_pow, ← v_xor]
  rfl
private theorem row_b7 : Data1792.second.row 7 = Pi.single (10 : Fin 1792) 1 := by
  have h : Data1792.secondRows[7]! = 1024 := by decide +kernel
  change v Data1792.secondRows[7]! = _
  rw [h]
  simp only [← v_pow]
  rfl
private theorem row_b8 : Data1792.second.row 8 = Pi.single (11 : Fin 1792) 1 := by
  have h : Data1792.secondRows[8]! = 2048 := by decide +kernel
  change v Data1792.secondRows[8]! = _
  rw [h]
  simp only [← v_pow]
  rfl
theorem singular_left_kernel : vecMul (Pi.single 0 1) singular = 0 := by
  simp only [singular, vecMul_add, ← vecMul_vecMul, add_vecMul, vecMul_one,
    single_one_vecMul, row_a0, row_a1, row_a2, row_a3, row_a4, row_a6, row_b0, row_b1, row_b2, row_b3, row_b4, row_b5, row_b6, row_b7, row_b8]
  ext j
  simp only [Pi.add_apply, Pi.zero_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
    show (8 : ZMod 2) = 0 by decide, show (10 : ZMod 2) = 0 by decide,
    mul_zero, zero_add]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
