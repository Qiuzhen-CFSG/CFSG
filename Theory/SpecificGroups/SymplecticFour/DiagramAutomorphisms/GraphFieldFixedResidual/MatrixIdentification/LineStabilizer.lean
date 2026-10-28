module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification.Generators

/-!
# The first-line stabilizer in the graph-field fixed subgroup

A fixed matrix stabilizing the first coordinate line is upper triangular:
three twisted-minor equations kill its remaining lower entries. Preservation
of the antidiagonal form determines the inverse diagonal pairs, and a further
minor equation identifies the diagonal with a Suzuki torus generator. After
removing that generator, the form and minor equations determine every entry
of a Suzuki root matrix. This proves an actual torus-root factorization and
membership in the generated Suzuki subgroup for every `m`, including zero.

This is the stabilizer calculation for the matrix identification underlying
Aschbacher--Smith 16.1.4(7), printed p.1171. The Suzuki generators use the
upper-triangular convention of Huppert--Blackburn III, XI.3.1--3.3. The full
fixed-group identification and the subsequent residual comparison are separate.
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification

private theorem lower_entries (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m)
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0) (h30 : A.val 3 0 = 0) :
    A.val 2 1 = 0 ∧ A.val 3 1 = 0 ∧ A.val 3 2 = 0 := by
  have hg : coordinateGraph A.val = A.val.map (suzukiTheta m) :=
    ((mem_fixedMatrixSubgroup_iff m A).mp hA).2
  have he (i j : Fin 4) := congrArg (fun M => M i j) hg
  have h21 : A.val 2 1 = 0 := by
    apply (suzukiTheta m).injective
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, h10, h30] using (he 2 1).symm
  have h31 : A.val 3 1 = 0 := by
    apply (suzukiTheta m).injective
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, h20, h30] using (he 3 1).symm
  have h32 : A.val 3 2 = 0 := by
    apply (suzukiTheta m).injective
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, h21, h31] using (he 3 2).symm
  exact ⟨h21, h31, h32⟩

private theorem diagonal_entries (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m)
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0) (h30 : A.val 3 0 = 0)
    (h21 : A.val 2 1 = 0) (h31 : A.val 3 1 = 0) (h32 : A.val 3 2 = 0) :
    A.val 0 0 ≠ 0 ∧ A.val 1 1 ≠ 0 ∧
      A.val 2 2 = (A.val 1 1)⁻¹ ∧ A.val 3 3 = (A.val 0 0)⁻¹ ∧
      A.val 0 0 = suzukiTheta m (A.val 1 1) * A.val 1 1 := by
  obtain ⟨hf, hg⟩ := (mem_fixedMatrixSubgroup_iff m A).mp hA
  change coordinateGraph A.val = A.val.map (suzukiTheta m) at hg
  have hc : A.val 0 0 * A.val 3 3 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, suzukiForm, h30, h31, h32] using
      congrArg (fun M => M 0 3) hf
  have hd : A.val 1 1 * A.val 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, suzukiForm, h10, h20, h21] using
      congrArg (fun M => M 1 2) hf
  have hc0 : A.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : A.val 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h22 : A.val 2 2 = (A.val 1 1)⁻¹ := eq_inv_of_mul_eq_one_right hd
  have h33 : A.val 3 3 = (A.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hc
  refine ⟨hc0, hd0, h22, h33, ?_⟩
  have ht : A.val 0 0 * (A.val 1 1)⁻¹ = suzukiTheta m (A.val 1 1) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, h20, h22] using
      congrArg (fun M => M 1 1) hg
  calc
    A.val 0 0 = (A.val 0 0 * (A.val 1 1)⁻¹) * A.val 1 1 := by simp [hd0]
    _ = _ := by rw [ht]

private theorem unitriangular_eq_root (m : ℕ) (U : GL (Fin 4) (SuzukiField m))
    (hU : U ∈ fixedMatrixSubgroup m)
    (h10 : U.val 1 0 = 0) (h20 : U.val 2 0 = 0) (h30 : U.val 3 0 = 0)
    (h21 : U.val 2 1 = 0) (h31 : U.val 3 1 = 0) (h32 : U.val 3 2 = 0)
    (h00 : U.val 0 0 = 1) (h11 : U.val 1 1 = 1)
    (h22 : U.val 2 2 = 1) (h33 : U.val 3 3 = 1) :
    U = SuzukiRootGL m (U.val 0 1) (U.val 0 2) := by
  obtain ⟨hf, hg⟩ := (mem_fixedMatrixSubgroup_iff m U).mp hU
  change coordinateGraph U.val = U.val.map (suzukiTheta m) at hg
  have h12 : U.val 1 2 = suzukiTheta m (U.val 0 1) := by
    simpa [coordinateGraph, coordinateFirst, coordinateSecond, h00, h10] using
      congrArg (fun M => M 0 1) hg
  have h23 : U.val 2 3 = U.val 0 1 := by
    have h : U.val 2 3 + U.val 0 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_four, suzukiForm, h00, h20, h21, h22, add_comm] using
        congrArg (fun M => M 0 2) hf
    simpa using (CharTwo.add_eq_iff_eq_add.mp h)
  have h13 : U.val 1 3 = U.val 0 1 * suzukiTheta m (U.val 0 1) + U.val 0 2 := by
    have h : U.val 1 3 + U.val 0 1 * suzukiTheta m (U.val 0 1) + U.val 0 2 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_four, suzukiForm, h00, h10, h11, h12, add_comm, add_left_comm, add_assoc] using
        congrArg (fun M => M 0 1) hf
    rw [add_assoc] at h
    simpa using (CharTwo.add_eq_iff_eq_add.mp h)
  have h03 : U.val 0 3 = (U.val 0 1)^2 * suzukiTheta m (U.val 0 1) +
      U.val 0 1 * U.val 0 2 + suzukiTheta m (U.val 0 2) := by
    have h : U.val 0 3 + U.val 0 1 *
        (U.val 0 1 * suzukiTheta m (U.val 0 1) + U.val 0 2) =
        suzukiTheta m (U.val 0 2) := by
      simpa [coordinateGraph, coordinateFirst, coordinateSecond, h11, h13, add_comm] using
        congrArg (fun M => M 0 2) hg
    rw [CharTwo.add_eq_iff_eq_add] at h
    calc
      U.val 0 3 = _ := h
      _ = _ := by ring
  apply Units.ext
  change U.val = SuzukiRootMatrix m (U.val 0 1) (U.val 0 2)
  rw [rootMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h11, h22, h33, h10, h20, h30, h21, h31, h32, h12, h23, h13, h03]

private theorem torus_inv (m : ℕ) (x : (SuzukiField m)ˣ) :
    SuzukiTorusGL m x⁻¹ = (SuzukiTorusGL m x)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      pow_ne_zero _ x.ne_zero]

/-- A fixed matrix stabilizing the first coordinate line factors into genuine
Suzuki torus and root generators, including over the field of two elements. -/
theorem fixed_line_stabilizer_factorization (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m)
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0) (h30 : A.val 3 0 = 0) :
    ∃ (x : (SuzukiField m)ˣ) (a b : SuzukiField m),
      A = SuzukiTorusGL m x * SuzukiRootGL m a b := by
  obtain ⟨h21, h31, h32⟩ := lower_entries m A hA h10 h20 h30
  obtain ⟨hc0, hd0, h22, h33, hc⟩ := diagonal_entries m A hA h10 h20 h30 h21 h31 h32
  let x : (SuzukiField m)ˣ := Units.mk0 (suzukiTheta m (A.val 1 1))
    ((map_ne_zero (suzukiTheta m)).mpr hd0)
  have hx : (x : SuzukiField m) = suzukiTheta m (A.val 1 1) := rfl
  have hhalf : (x : SuzukiField m) ^ (2 ^ m) = A.val 1 1 := by
    apply (suzukiTheta m).injective
    rw [suzukiTheta_half, hx]
  have houter : (x : SuzukiField m) ^ (1 + 2 ^ m) = A.val 0 0 := by
    rw [pow_add, pow_one, hhalf, hx, hc]
  have hinv : (SuzukiTorusGL m x⁻¹).val =
      !![(A.val 0 0)⁻¹,0,0,0;
        0,(A.val 1 1)⁻¹,0,0;
        0,0,A.val 1 1,0;
        0,0,0,A.val 0 0] := by
    simp [SuzukiTorusGL, SuzukiTorusMatrix, hhalf, houter]
  let U := SuzukiTorusGL m x⁻¹ * A
  have hU : U ∈ fixedMatrixSubgroup m :=
    (fixedMatrixSubgroup m).mul_mem (torus_mem_fixedMatrixSubgroup m x⁻¹) hA
  have hval : U.val =
      !![(A.val 0 0)⁻¹,0,0,0;
        0,(A.val 1 1)⁻¹,0,0;
        0,0,A.val 1 1,0;
        0,0,0,A.val 0 0] * A.val := by
    change (SuzukiTorusGL m x⁻¹).val * A.val = _
    rw [hinv]
  have hroot : U = SuzukiRootGL m (U.val 0 1) (U.val 0 2) := by
    apply unitriangular_eq_root m U hU
    all_goals simp [hval, Matrix.mul_apply, Fin.sum_univ_four,
      h10, h20, h30, h21, h31, h32, h22, h33, hc0, hd0]
  refine ⟨x, U.val 0 1, U.val 0 2, ?_⟩
  rw [← hroot]
  change A = SuzukiTorusGL m x * (SuzukiTorusGL m x⁻¹ * A)
  rw [torus_inv, mul_inv_cancel_left]

/-- Every graph-field fixed matrix stabilizing the first coordinate line belongs
to the subgroup generated by the Suzuki matrices. -/
theorem fixed_line_stabilizer_mem_suzuki (m : ℕ) (A : GL (Fin 4) (SuzukiField m))
    (hA : A ∈ fixedMatrixSubgroup m)
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0) (h30 : A.val 3 0 = 0) :
    A ∈ SuzukiMatrixSubgroup m := by
  obtain ⟨x, a, b, rfl⟩ := fixed_line_stabilizer_factorization m A hA h10 h20 h30
  apply (SuzukiMatrixSubgroup m).mul_mem
  · exact Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))
  · exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
