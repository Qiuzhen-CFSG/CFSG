module

public import Theory.LinearAlgebra.ZModFourPlaneCorrection

/-!
# Root-preserving correction in a cyclic-four plane extension

The determinant-one correction can be chosen with square either zero or
the first marked binary point. In the original HS construction the square
preimage of that point is exactly the overlap with its point core, so this
extra coordinate control preserves the first actual point-core membership.

The private certificates classify individual lifts using nine binary
perturbation entries and then check the explicit correction on four-bit
normal forms. They enumerate neither automorphism groups nor ambient groups.
-/

namespace ZModFourRootCorrection

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
        v - (secondForm q).mulVec v = ![2, 2, 0] ∧
        v + v = ![2, 0, 0] := by
  decide +kernel

/-- A two-torsion product norm admits an involutory correction whose square
lies in the first marked root line. -/
public theorem exists_root_inverted_displacement
    (A B : Matrix (Fin 3) (Fin 3) (ZMod 4))
    (hA : A ^ 2 = 1) (hB : B ^ 2 = 1) (hcomm : A * B = B * A)
    (hAdet : A.det = 1) (hBdet : B.det = 1)
    (hAmod : A.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1])
    (hBmod : B.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1])
    (c : Fin 3 → ZMod 4) (hc : c + c = 0)
    (hnorm : ∃ d, c = d + (A * B).mulVec d) :
    ∃ p : Fin 3 → ZMod 4, p + A.mulVec p = 0 ∧ p - B.mulVec p = c ∧
      (p + p = 0 ∨ p + p = ![2, 0, 0]) := by
  obtain ⟨X, rfl⟩ := matrix_lift A first hAmod
  obtain ⟨Y, rfl⟩ := matrix_lift B second hBmod
  rw [first_form_certificate X hA hAdet, second_form_certificate Y hB hBdet] at hcomm hnorm ⊢
  obtain ⟨d, rfl⟩ := hnorm
  rcases norm_certificate _ _ hcomm d hc with hz | ht
  · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [hz]
  · exact ⟨_, (correction_certificate _ _ hcomm).1,
      (correction_certificate _ _ hcomm).2.1.trans ht.symm,
      Or.inr (correction_certificate _ _ hcomm).2.2⟩

end ZModFourRootCorrection
