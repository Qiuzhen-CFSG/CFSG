module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Geometry
public import Theory.SpecificGroups.SU3.FullCentralizer

/-!
# The coordinate-line stabilizer in SU₄(3)

The stabilizer preserves the first coordinate line and its Hermitian orthogonal
complement, so both mixed matrix blocks vanish. The determinant-one equation
forces its first entry to be the inverse determinant of the remaining block.
Conversely every full unitary three-dimensional matrix gives such a stabilizer.
This constructs an actual multiplicative equivalence with GU₃(3).

The matrices are over `FiniteField.Nine`, with the identity Hermitian form and
cube conjugation. Source: the unitary conventions of GLS3, chapter 2, §2.7
(`refs/KGroup/GLS3/chapter2.tex`). This is the linear calculation underlying the
nondegenerate line case used in Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4,482 of `refs/quasithin.pdf`. The projective quotient is treated in
`Line.Scalars` and `Line`; no stabilizer classification is assumed.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line

/-- The full unitary group, with no determinant restriction. -/
abbrev FullUnitaryThree := (form 3).unitarySubgroup

/-- A scalar first coordinate and a three-dimensional diagonal block. -/
@[expose] def block (a : FiniteField.Nine) (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) :
    Matrix (Fin 4) (Fin 4) FiniteField.Nine :=
  Fin.cases (Fin.cases a (fun _ => 0)) (fun i => Fin.cases 0 (B i))

@[simp] theorem block_zero_zero (a : FiniteField.Nine)
    (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) : block a B 0 0 = a := by rfl

@[simp] theorem block_zero_succ (a : FiniteField.Nine)
    (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) (j : Fin 3) :
    block a B 0 j.succ = 0 := by rfl

@[simp] theorem block_succ_zero (a : FiniteField.Nine)
    (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) (i : Fin 3) :
    block a B i.succ 0 = 0 := by rfl

@[simp] theorem block_succ_succ (a : FiniteField.Nine)
    (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) (i j : Fin 3) :
    block a B i.succ j.succ = B i j := by rfl

private theorem block_one : block 1 1 = 1 := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, eq_comm]

private theorem block_mul (a b : FiniteField.Nine) (B C : Matrix (Fin 3) (Fin 3) FiniteField.Nine) :
    block a B * block b C = block (a * b) (B * C) := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_adj (a : FiniteField.Nine) (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) :
    (block a B).conjTranspose = block (star a) B.conjTranspose := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

private theorem block_det (a : FiniteField.Nine) (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine) :
    (block a B).det = a * B.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [block_zero_zero, block_zero_succ, Fin.val_zero, pow_zero, one_mul,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
  rfl

private def blockGL (B : GL (Fin 3) FiniteField.Nine) : GL (Fin 4) FiniteField.Nine where
  val := block B.val.det⁻¹ B.val
  inv := block (B⁻¹).val.det⁻¹ (B⁻¹).val
  val_inv := by
    rw [block_mul, ← mul_inv, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one,
      inv_one, block_one]
  inv_val := by
    rw [block_mul, ← mul_inv, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
      inv_one, block_one]

private theorem blockGL_det (B : GL (Fin 3) FiniteField.Nine) : GeneralLinearGroup.det (blockGL B) = 1 := by
  apply Units.ext
  change (block B.val.det⁻¹ B.val).det = 1
  rw [block_det, inv_mul_cancel₀ (GeneralLinearGroup.det_ne_zero B)]

/-- Unitarity forces the determinant to have norm one. -/
theorem det_norm (B : FullUnitaryThree) : star B.val.val.det * B.val.val.det = 1 :=
  Matrix.SU3.unitary_det_norm (form 3) rfl B

/-- For cube conjugation, norm one means fourth power one. -/
theorem det_pow_four (B : FullUnitaryThree) : B.val.val.det ^ 4 = 1 := by
  simpa only [FiniteField.Nine.star_eq_cube, ← pow_succ] using det_norm B

private theorem blockGL_unitary (B : FullUnitaryThree) : blockGL B.val ∈ (form 4).unitarySubgroup := by
  change (block B.val.val.det⁻¹ B.val.val).conjTranspose * 1 *
    block B.val.val.det⁻¹ B.val.val = 1
  have hB : B.val.val.conjTranspose * B.val.val = 1 := by
    have h := B.property
    change B.val.val.conjTranspose * 1 * B.val.val = 1 at h
    simpa using h
  rw [mul_one, block_adj, block_mul, hB, star_inv₀, ← mul_inv, det_norm B, inv_one,
    block_one]

/-- The embedding `B ↦ diag(det(B)⁻¹, B)` into SU₄. -/
def blockEmbedding : FullUnitaryThree →* (form 4).specialSubgroup where
  toFun B := ⟨blockGL B.val, blockGL_unitary B, blockGL_det B.val⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change block (1 : Matrix (Fin 3) (Fin 3) FiniteField.Nine).det⁻¹ 1 = 1
    rw [Matrix.det_one, inv_one, block_one]
  map_mul' B C := by
    apply Subtype.ext
    apply Units.ext
    change block (B.val.val * C.val.val).det⁻¹ (B.val.val * C.val.val) =
      block B.val.val.det⁻¹ B.val.val * block C.val.val.det⁻¹ C.val.val
    rw [block_mul, Matrix.det_mul, mul_inv]

/-- The embedding has the advertised determinant-corrected matrix. -/
theorem blockEmbedding_val (B : FullUnitaryThree) :
    (blockEmbedding B).val.val = block B.val.val.det⁻¹ B.val.val := by rfl

private theorem mem_line (v : Space 4) :
    v ∈ coordinateSubspace 1 ↔ ∀ i : Fin 3, v i.succ = 0 := by
  constructor
  · intro h i
    exact h i.succ (Nat.succ_le_succ (Nat.zero_le _))
  · intro h i
    refine Fin.cases ?_ (fun j _ => h j) i
    simp

private theorem block_mulVec_succ (a : FiniteField.Nine) (B : Matrix (Fin 3) (Fin 3) FiniteField.Nine)
    (v : Space 4) (i : Fin 3) :
    (block a B *ᵥ v) i.succ = (B *ᵥ (fun j => v j.succ)) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem blockEmbedding_mem (B : FullUnitaryThree) :
    blockEmbedding B ∈ specialStabilizer (coordinateSubspace 1) := by
  rw [mem_specialStabilizer_iff]
  intro v
  rw [mem_line, mem_line]
  rw [blockEmbedding_val]
  simp only [block_mulVec_succ]
  constructor
  · intro h
    have hz : B.val.val *ᵥ (fun j => v j.succ) = 0 := funext h
    have hi := congrArg (fun w => (B.val⁻¹).val *ᵥ w) hz
    simp only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at hi
    exact fun j => congrFun hi j
  · intro h
    have hz : (fun j : Fin 3 => v j.succ) = 0 := funext h
    simp [hz]

private theorem first_column (g : specialStabilizer (coordinateSubspace 1)) (i : Fin 3) :
    g.val.val.val i.succ 0 = 0 := by
  have h := ((mem_specialStabilizer_iff _ g.val).mp g.property
    (Pi.single 0 1)).mpr (by rw [mem_line]; intro j; simp)
  have he := (mem_line _).mp h i
  simpa using he

private theorem first_row (g : specialStabilizer (coordinateSubspace 1)) (j : Fin 3) :
    g.val.val.val 0 j.succ = 0 := by
  have ho := specialStabilizer_le_orthogonal (coordinateSubspace 1) g.property
  have hv : Pi.single j.succ (1 : FiniteField.Nine) ∈ orthogonal (coordinateSubspace 1) := by
    intro w hw
    simpa [pairing] using congrArg star ((mem_line w).mp hw j)
  have h := ((mem_specialStabilizer_iff _ g.val).mp ho _).mpr hv
  have he := h (Pi.single 0 1) (by rw [mem_line]; intro i; simp)
  simpa [pairing] using he

private theorem matrix_block (g : specialStabilizer (coordinateSubspace 1)) :
    g.val.val.val = block (g.val.val.val 0 0) (g.val.val.val.submatrix Fin.succ Fin.succ) := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · exact first_row g j
  · exact first_column g i
  · rfl

private theorem blockEmbedding_surj (g : specialStabilizer (coordinateSubspace 1)) :
    ∃ B : FullUnitaryThree, blockEmbedding B = g.val := by
  let C := g.val.val.val.submatrix Fin.succ Fin.succ
  have gp := ((form 4).mem_specialSubgroup_iff g.val.val).mp g.val.property
  have hd := congrArg (fun u : FiniteField.Nineˣ => u.val) gp.2
  change g.val.val.val.det = 1 at hd
  have hdet : g.val.val.val 0 0 * C.det = 1 := by
    rw [matrix_block g, block_det] at hd
    exact hd
  have hC : C.det ≠ 0 := by intro h; rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  let B : GL (Fin 3) FiniteField.Nine := GeneralLinearGroup.mkOfDetNeZero C hC
  have ha : g.val.val.val 0 0 = C.det⁻¹ := (mul_eq_one_iff_eq_inv₀ hC).mp hdet
  have hg : g.val.val.val = block C.det⁻¹ C := by rw [matrix_block g, ha]
  have hu : C.conjTranspose * C = 1 := by
    have h := gp.1
    change g.val.val.val.conjTranspose * 1 * g.val.val.val = 1 at h
    rw [mul_one, hg, block_adj, block_mul] at h
    apply Matrix.ext
    intro i j
    simpa only [block_succ_succ, Matrix.one_apply, Fin.succ_inj] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine => M i.succ j.succ) h
  have hBU : B ∈ (form 3).unitarySubgroup := by
    change C.conjTranspose * 1 * C = 1
    simpa using hu
  refine ⟨⟨B, hBU⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hg.symm

theorem blockEmbedding_injective : Function.Injective blockEmbedding := by
  intro B C h
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hm := congrArg (fun A : (form 4).specialSubgroup => A.val.val) h
  rw [blockEmbedding_val, blockEmbedding_val] at hm
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine => M i.succ j.succ) hm

theorem blockEmbedding_range : blockEmbedding.range = specialStabilizer (coordinateSubspace 1) := by
  ext g
  constructor
  · rintro ⟨B, rfl⟩
    exact blockEmbedding_mem B
  · intro hg
    exact blockEmbedding_surj ⟨g, hg⟩

/-- The full SU₄ coordinate-line stabilizer is isomorphic to GU₃(3). -/
def blockEquiv : FullUnitaryThree ≃* specialStabilizer (coordinateSubspace 1) :=
  (MonoidHom.ofInjective blockEmbedding_injective).trans
    (MulEquiv.subgroupCongr blockEmbedding_range)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line
