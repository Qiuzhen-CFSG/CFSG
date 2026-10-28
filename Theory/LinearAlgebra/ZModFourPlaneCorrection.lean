module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Correcting a two-torsion norm for a lifted binary plane group

Two commuting determinant-one involutions on (Z/4)³ whose reductions are
the standard pointwise plane transvections have a small explicit normal
form. Each individual lift has four binary parameters. The commuting
pairs have six parameters. A norm for their product which is killed by
two is either zero or (2,2,0); the latter is the displacement under the
second actor of an element inverted by the first.

This supplies the linear correction in the actual HS plane-centralizer
extension. It does not assert splitting for arbitrary locally split
extensions: the two-torsion hypothesis on the norm is essential.
-/

namespace ZModFourPlaneCorrection

private abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 4)
private abbrev BinaryMat := Matrix (Fin 3) (Fin 3) (ZMod 2)
private abbrev Vec := Fin 3 → ZMod 4
private abbrev Parameters := Fin 4 → ZMod 2
private def reduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _
private def first : BinaryMat := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
private def second : BinaryMat := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
private def lift (D X : BinaryMat) : Mat := fun i j =>
  (D i j).val + 2 * (X i j).val
private def firstForm (p : Parameters) : Mat :=
  !![1 + 2 * (p 0).val, 2 * (p 1).val, 1 + 2 * (p 2).val;
     0, 3, 2 * (p 3).val;
     0, 0, 3 + 2 * (p 0).val]
private def secondForm (p : Parameters) : Mat :=
  !![3, 0, 2 * (p 3).val;
     2 * (p 1).val, 1 + 2 * (p 0).val, 1 + 2 * (p 2).val;
     0, 0, 3 + 2 * (p 0).val]

private theorem scalar_lift : ∀ a : ZMod 4, ∀ b : ZMod 2,
    reduction a = b → ∃ t : ZMod 2, a = b.val + 2 * t.val := by
  decide +kernel

private theorem reduction_of_doubling : ∀ a : ZMod 4, ∀ b : ZMod 2,
    a * 2 = 2 * (b.val : ZMod 4) → reduction a = b := by
  decide +kernel

/-- The action on the three marked involutions determines the binary
reduction, so an actual action formula supplies the normal-form hypotheses. -/
public theorem reduction_eq_of_doubled_basis
    (A : Matrix (Fin 3) (Fin 3) (ZMod 4))
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : ∀ j, A.mulVec (Pi.single j 2) = fun i => 2 * ((B i j).val : ZMod 4)) :
    A.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) = B := by
  ext i j
  apply reduction_of_doubling
  have hh := congrFun (h j) i
  simpa only [Matrix.mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply] using hh

private theorem matrix_lift (A : Mat) (D : BinaryMat) (h : A.map reduction = D) :
    ∃ X : BinaryMat, A = lift D X := by
  have hh (i j : Fin 3) : ∃ t : ZMod 2, A i j = (D i j).val + 2 * t.val :=
    scalar_lift (A i j) (D i j) (congrArg (fun B : BinaryMat => B i j) h)
  choose X hX using hh
  exact ⟨X, Matrix.ext hX⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem first_form_certificate : ∀ X : BinaryMat,
    lift first X ^ 2 = 1 → (lift first X).det = 1 →
      lift first X = firstForm ![X 0 0, X 0 1, X 0 2, X 1 2] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem second_form_certificate : ∀ X : BinaryMat,
    lift second X ^ 2 = 1 → (lift second X).det = 1 →
      lift second X = secondForm ![X 1 1, X 1 0, X 1 2, X 0 2] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem norm_certificate : ∀ p q : Parameters,
    firstForm p * secondForm q = secondForm q * firstForm p → ∀ d : Vec,
      let c := d + (firstForm p * secondForm q).mulVec d
      c + c = 0 → c = 0 ∨ c = ![2, 2, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem correction_certificate : ∀ p q : Parameters,
    firstForm p * secondForm q = secondForm q * firstForm p →
      let v : Vec := ![1, 0, firstForm p 0 0 + 1]
      v + (firstForm p).mulVec v = 0 ∧
        v - (secondForm q).mulVec v = ![2, 2, 0] := by
  decide +kernel

/-- A two-torsion product norm can be removed by changing only the first
involutory lift, while keeping that lift involutory. -/
public theorem exists_inverted_displacement
    (A B : Matrix (Fin 3) (Fin 3) (ZMod 4))
    (hA : A ^ 2 = 1) (hB : B ^ 2 = 1) (hcomm : A * B = B * A)
    (hAdet : A.det = 1) (hBdet : B.det = 1)
    (hAmod : A.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1])
    (hBmod : B.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1])
    (c : Fin 3 → ZMod 4) (hc : c + c = 0)
    (hnorm : ∃ d, c = d + (A * B).mulVec d) :
    ∃ p : Fin 3 → ZMod 4, p + A.mulVec p = 0 ∧ p - B.mulVec p = c := by
  obtain ⟨X, rfl⟩ := matrix_lift A first hAmod
  obtain ⟨Y, rfl⟩ := matrix_lift B second hBmod
  rw [first_form_certificate X hA hAdet, second_form_certificate Y hB hBdet] at hcomm hnorm ⊢
  obtain ⟨d, rfl⟩ := hnorm
  rcases norm_certificate _ _ hcomm d hc with hz | ht
  · refine ⟨0, ?_, ?_⟩ <;> simp [hz]
  · exact ⟨_, (correction_certificate _ _ hcomm).1,
      (correction_certificate _ _ hcomm).2.trans ht.symm⟩

end ZModFourPlaneCorrection
