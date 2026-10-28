module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction

/-!
# The plane radical matrix commutant

Conjugating by the flag basis changes the ambient plane-radical matrices to
`[[I,x,z],[0,1,x*],[0,0,I]]`.  Two trace-one lifts, with `x` equal to the
two standard basis vectors, force a commuting matrix to be scalar on the
three diagonal blocks, zero on the other blocks, and arbitrary in the
upper-right two-by-two block.  Conjugating back gives `planeCentralMatrix`.

The only scalar input is `c + J.conj c = 1`; no invertibility, unitarity,
normality, finiteness, or Frobenius hypothesis is used.

Source: the elementary characteristic-two parabolic calculation underlying
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(7),
printed pp.263--264 of `refs/quasithin.pdf`.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
variable {F : Type*} [Field F] [CharP F 2]
open Theory.SpecificGroups.UnitaryFive

private def p0 (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) : PlaneCore.Parameters J :=
  ⟨![1, 0], !![c, 0; 0, 0], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  ⟩
private def p1 (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) : PlaneCore.Parameters J :=
  ⟨![0, 1], !![0, 0; 0, c], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  ⟩

private theorem plane_commutant_in_coordinates (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1)
    (C : Matrix (Fin 5) (Fin 5) F)
    (h : ∀ u : PlaneCore.Parameters J,
      C * PlaneCore.Parameters.matrix u = PlaneCore.Parameters.matrix u * C) :
    ∃ (a : F) (z : Matrix (Fin 2) (Fin 2) F),
      C = !![a,0,0,z 0 0,z 0 1;
             0,a,0,z 1 0,z 1 1;
             0,0,a,0,0;
             0,0,0,a,0;
             0,0,0,0,a] := by
  let u0 := p0 J c hc
  let u1 := p1 J c hc
  have h0 := h u0
  have h1 := h u1
  have e0 (i j : Fin 5) := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) h0
  have e1 (i j : Fin 5) := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) h1
  have r00 := e1 0 0
  have r01 := e1 0 1
  have r02 := e1 0 2
  have r03 := e1 0 3
  have r04 := e1 0 4
  have r10 := e1 1 0
  have r11 := e1 1 1
  have r12 := e1 1 2
  have r13 := e1 1 3
  have r14 := e1 1 4
  have r20 := e1 2 0
  have r21 := e1 2 1
  have r22 := e1 2 2
  have r23 := e1 2 3
  have r24 := e1 2 4
  have r30 := e1 3 0
  have r31 := e1 3 1
  have r32 := e1 3 2
  have r33 := e1 3 3
  have r34 := e1 3 4
  have r40 := e1 4 0
  have r41 := e1 4 1
  have r42 := e1 4 2
  have r43 := e1 4 3
  have r44 := e1 4 4
  have q00 := e0 0 0
  have q01 := e0 0 1
  have q02 := e0 0 2
  have q03 := e0 0 3
  have q04 := e0 0 4
  have q10 := e0 1 0
  have q11 := e0 1 1
  have q12 := e0 1 2
  have q13 := e0 1 3
  have q14 := e0 1 4
  have q20 := e0 2 0
  have q21 := e0 2 1
  have q22 := e0 2 2
  have q23 := e0 2 3
  have q24 := e0 2 4
  have q30 := e0 3 0
  have q31 := e0 3 1
  have q32 := e0 3 2
  have q33 := e0 3 3
  have q34 := e0 3 4
  have q40 := e0 4 0
  have q41 := e0 4 1
  have q42 := e0 4 2
  have q43 := e0 4 3
  have q44 := e0 4 4
  simp [u0, p0, PlaneCore.Parameters.matrix, Matrix.mul_apply,
    Fin.sum_univ_succ] at q00 q01 q02 q03 q04 q10 q11 q12 q13 q14 q20 q21 q22 q23 q24 q30 q31 q32 q33 q34 q40 q41 q42 q43 q44
  simp [u1, p1, PlaneCore.Parameters.matrix, Matrix.mul_apply,
    Fin.sum_univ_succ] at r00 r01 r02 r03 r04 r10 r11 r12 r13 r14 r20 r21 r22 r23 r24 r30 r31 r32 r33 r34 r40 r41 r42 r43 r44
  have hc0 : c ≠ 0 := by
    have htwo : (1 + 1 : F) = 0 := by
      calc
        (1 + 1 : F) = 2 := by ring
        _ = 0 := CharTwo.two_eq_zero
    intro hcz
    exact (one_ne_zero : (1 : F) ≠ 0) (by
      calc
        (1 : F) = c + J.conj c := hc.symm
        _ = 0 := by simp [hcz]
        _ = 1 + 1 := htwo.symm
        _ = 0 := htwo)
  have h30 : C 3 0 = 0 := by exact q20
  have h31 : C 3 1 = 0 := by exact q21
  have h40 : C 4 0 = 0 := by exact r20
  have h41 : C 4 1 = 0 := by exact r21
  have h20 : C 2 0 = 0 := by
    simpa [h30] using q00
  have h21 : C 2 1 = 0 := by
    simpa [h31] using q01
  have h42 : C 4 2 = 0 := by
    rw [h40] at q43
    simp only [zero_mul, zero_add] at q43
    apply add_right_cancel (b := C 4 3)
    simpa [add_comm] using q43
  have h32 : C 3 2 = 0 := by
    rw [h30] at q33
    simp only [zero_mul, zero_add] at q33
    apply add_right_cancel (b := C 3 3)
    simpa [add_comm] using q33
  have h22 : C 0 0 = C 2 2 := by
    rw [h32] at q02
    simp only [mul_zero, add_zero] at q02
    linear_combination q02
  have h11 : C 1 1 = C 2 2 := by
    rw [h42] at r12
    simp only [mul_zero, add_zero] at r12
    linear_combination r12
  have h33 : C 3 3 = C 2 2 := by
    rw [h20] at q23
    simp only [zero_mul, zero_add] at q23
    apply add_right_cancel (b := C 2 3)
    rw [add_comm (C 2 3) (C 3 3)] at q23
    exact q23.symm
  have h43 : C 4 3 = 0 := by exact r23
  have h23 : C 2 3 = 0 := by
    rw [h43] at r13
    simpa using r13
  have h44 : C 4 4 = C 2 2 := by
    rw [h21] at r24
    simp only [zero_mul, zero_add] at r24
    apply add_right_cancel (b := C 2 4)
    rw [add_comm (C 2 4) (C 4 4)] at r24
    exact r24.symm
  have h01 : C 0 1 = 0 := by exact r02
  have h10 : C 1 0 = 0 := by exact q12
  have h12 : C 1 2 = 0 := by
    rw [h10] at q13
    simp only [zero_mul, zero_add] at q13
    apply add_right_cancel (b := C 1 3)
    simpa [add_comm] using q13
  have h02 : C 0 2 = 0 := by
    rw [h23] at q03
    simp only [zero_add] at q03
    linear_combination q03 - c * h22 + c * h33
  have h34 : C 3 4 = 0 := by exact q24
  have h24 : C 2 4 = 0 := by
    rw [h34] at q04
    linear_combination q04
  let a := C 0 0
  let z : Matrix (Fin 2) (Fin 2) F := !![C 0 3, C 0 4; C 1 3, C 1 4]
  refine ⟨a, z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a, z, h01, h02, h10, h11, h12, h20, h21,
      h22, h23, h24, h30, h31, h32, h33, h34, h40, h41, h42, h43, h44]

theorem plane_commutant_normal_form (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1)
    (A : Matrix (Fin 5) (Fin 5) F)
    (hA : ∀ v : PlaneCore.Parameters J,
      A * PlaneCore.Parameters.ambientMatrix v =
        PlaneCore.Parameters.ambientMatrix v * A) :
    ∃ (a : F) (z : Matrix (Fin 2) (Fin 2) F),
      A = planeCentralMatrix a z := by
  let C : Matrix (Fin 5) (Fin 5) F :=
    PlaneCore.flagBasisInv * A * PlaneCore.flagBasis
  have hC (v : PlaneCore.Parameters J) :
      C * PlaneCore.Parameters.matrix v = PlaneCore.Parameters.matrix v * C := by
    have hh := congrArg
      (fun X : Matrix (Fin 5) (Fin 5) F => PlaneCore.flagBasisInv * X * PlaneCore.flagBasis)
      (hA v)
    rw [PlaneCore.Parameters.ambientMatrix_eq] at hh
    calc
      C * PlaneCore.Parameters.matrix v =
          PlaneCore.flagBasisInv *
            (A * (PlaneCore.flagBasis * PlaneCore.Parameters.matrix v *
              PlaneCore.flagBasisInv)) * PlaneCore.flagBasis := by
        simp only [C, mul_assoc]
        rw [PlaneCore.flagBasis_inv_mul]
        simp
      _ = PlaneCore.flagBasisInv *
          (PlaneCore.flagBasis * PlaneCore.Parameters.matrix v *
            PlaneCore.flagBasisInv * A) * PlaneCore.flagBasis := by
        exact hh
      _ = PlaneCore.Parameters.matrix v * C := by
        simp only [C, mul_assoc]
        rw [← mul_assoc PlaneCore.flagBasisInv PlaneCore.flagBasis]
        rw [PlaneCore.flagBasis_inv_mul]
        simp
  obtain ⟨a, z, hz⟩ := plane_commutant_in_coordinates J c hc C hC
  refine ⟨a, z, ?_⟩
  have hC' : C = !![a,0,0,z 0 0,z 0 1;
             0,a,0,z 1 0,z 1 1;
             0,0,a,0,0;
             0,0,0,a,0;
             0,0,0,0,a] := hz
  rw [show A = PlaneCore.flagBasis * C * PlaneCore.flagBasisInv by
    simp only [C, mul_assoc]
    rw [← mul_assoc PlaneCore.flagBasis PlaneCore.flagBasisInv]
    rw [PlaneCore.flagBasis_mul_inv]
    simp]
  rw [hC']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeCentralMatrix, PlaneCore.flagBasis, PlaneCore.flagBasisInv,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]
end Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
