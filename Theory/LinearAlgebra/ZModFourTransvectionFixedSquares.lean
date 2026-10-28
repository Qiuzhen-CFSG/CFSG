module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Fixed squares for a determinant-one lifted binary transvection

An involution on the cyclic-four cube reducing to the second standard
binary shear cannot fix a square root of the first binary point. The
four-parameter normal form has first row (3,0,2d); a square root of that
point has odd first coordinate and even third coordinate.

The private certificates use nine binary perturbation entries to obtain
the four-bit normal form, then check its fixed vectors. They do not
enumerate an ambient group or an automorphism group.
-/

namespace ZModFourTransvectionFixedSquares

private abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 4)
private abbrev BinaryMat := Matrix (Fin 3) (Fin 3) (ZMod 2)
private abbrev Vec := Fin 3 → ZMod 4
private abbrev Parameters := Fin 4 → ZMod 2
private def reduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _
private def second : BinaryMat := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
private def lift (X : BinaryMat) : Mat := fun i j =>
  (second i j).val + 2 * (X i j).val
private def secondForm (p : Parameters) : Mat :=
  !![3, 0, 2 * (p 3).val;
     2 * (p 1).val, 1 + 2 * (p 0).val, 1 + 2 * (p 2).val;
     0, 0, 3 + 2 * (p 0).val]

private theorem scalar_lift : ∀ a : ZMod 4, ∀ b : ZMod 2,
    reduction a = b → ∃ t : ZMod 2, a = b.val + 2 * t.val := by
  decide +kernel

private theorem matrix_lift (B : Mat) (h : B.map reduction = second) :
    ∃ X : BinaryMat, B = lift X := by
  have hh (i j : Fin 3) : ∃ t : ZMod 2,
      B i j = (second i j).val + 2 * t.val :=
    scalar_lift (B i j) (second i j) (congrArg (fun A : BinaryMat => A i j) h)
  choose X hX using hh
  exact ⟨X, Matrix.ext hX⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem second_form_certificate : ∀ X : BinaryMat,
    lift X ^ 2 = 1 → (lift X).det = 1 →
      lift X = secondForm ![X 1 1, X 1 0, X 1 2, X 0 2] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem fixed_square_certificate : ∀ p : Parameters, ∀ c : Vec,
    c + c = ![2, 0, 0] → (secondForm p).mulVec c ≠ c := by
  decide +kernel

/-- A determinant-one involutory lift of the second binary shear fixes no
square root of the first marked binary point. -/
public theorem not_fixed_of_double_first
    (B : Matrix (Fin 3) (Fin 3) (ZMod 4)) (hB : B ^ 2 = 1) (hdet : B.det = 1)
    (hmod : B.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1])
    (c : Fin 3 → ZMod 4) (hc : c + c = ![2, 0, 0]) : B.mulVec c ≠ c := by
  obtain ⟨X, rfl⟩ := matrix_lift B hmod
  rw [second_form_certificate X hB hdet]
  exact fixed_square_certificate _ c hc

end ZModFourTransvectionFixedSquares
