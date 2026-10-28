module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal.ShearNormalizer

/-!
# The two unitary-five parabolics are two-local

The ambient projective images of the line and plane shear subgroups are
nonidentity two-subgroups. Their ambient normalizers are exactly the full
projective line and plane parabolics. In particular these actual parabolics
are two-local in PSU, as required for PSU₅(4).

For the line, interchanging coordinates zero and one gives a shear whose
displacements fill the line. For the plane, simultaneously interchanging
zero/one and two/three gives a shear whose displacements fill the plane.
The normalizer therefore preserves the relevant subspace, including after
projectivization by the involution-lifting argument in `ShearNormalizer`.
The off-diagonal entry of the first interchange proves nontriviality in PSU.

The proof works over every finite field of characteristic two with identity
Gram matrix. Thus the field-order-sixteen and fourth-power-conjugation
hypotheses of the PSU₅(4) application require no further model facts here.
No isotropic transitivity or full unipotent-radical decomposition is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed p.4 (Theorem 0.1.1(1), p.482), and the unitary-five
parabolics in F.1.12(7), printed pp.263--264, in `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [CharP F 2]

private theorem lineSwap_ambient_shear (J : HermitianForm 5 F) (hJ : J.form = 1) :
    lineSwap J hJ ∈ shearSubgroup (linearAction J) (line F) :=
  lineSwap_mem_shears J hJ

private theorem line_displacements (J : HermitianForm 5 F) (hJ : J.form = 1)
    (v : Fin 5 → F) (hv : v ∈ line F) :
    ∃ a ∈ shearSubgroup (linearAction J) (line F), ∃ w, linearAction J a w - w = v := by
  refine ⟨lineSwap J hJ, lineSwap_ambient_shear J hJ, ![0, v 0, 0, 0, 0], ?_⟩
  rw [lineSwap_apply]
  change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
  ext i
  fin_cases i <;> simp [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, CharTwo.neg_eq]

/-- The simultaneous interchanges of coordinates zero/one and two/three. -/
private def planeSwapMatrix : Matrix (Fin 5) (Fin 5) F :=
  (1 : Matrix (Fin 5) (Fin 5) F).submatrix
    (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5)) id

omit [CharP F 2] in
private theorem planeSwapMatrix_sq :
    (planeSwapMatrix : Matrix (Fin 5) (Fin 5) F) * planeSwapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Equiv.swap_apply_def]

private def planeSwapGL : GL (Fin 5) F :=
  ⟨planeSwapMatrix, planeSwapMatrix, planeSwapMatrix_sq, planeSwapMatrix_sq⟩

omit [CharP F 2] in
private theorem planeSwapMatrix_det :
    (planeSwapMatrix : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [planeSwapMatrix, Matrix.det_permute]
  simp

set_option maxRecDepth 2048 in
private def planeSwap (J : HermitianForm 5 F) (hJ : J.form = 1) : J.specialSubgroup := by
  refine ⟨planeSwapGL, ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · have hc : J.conjTranspose planeSwapMatrix = planeSwapMatrix := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, planeSwapMatrix, Matrix.one_apply,
          Equiv.swap_apply_def]
    change J.conjTranspose planeSwapMatrix * J.form * planeSwapMatrix = J.form
    rw [hJ, hc, mul_one, planeSwapMatrix_sq]
  · exact Units.ext (planeSwapMatrix_det (F := F))

omit [CharP F 2] in
private theorem planeSwap_apply (J : HermitianForm 5 F) (hJ : J.form = 1) (v : Fin 5 → F) :
    linearAction J (planeSwap J hJ) v = ![v 1, v 0, v 3, v 2, v 4] := by
  change planeSwapMatrix *ᵥ v = _
  ext i
  fin_cases i <;>
    simp [planeSwapMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Equiv.swap_apply_def]

private theorem planeSwap_ambient_shear (J : HermitianForm 5 F) (hJ : J.form = 1) :
    planeSwap J hJ ∈ shearSubgroup (linearAction J) (plane F) := by
  constructor
  · intro v hv
    rw [planeSwap_apply]
    change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
    ext i
    fin_cases i <;> simp [hv.1, hv.2.1]
  · intro v
    rw [planeSwap_apply]
    change v 0 - v 1 = v 1 - v 0 ∧ v 2 - v 3 = v 3 - v 2 ∧ v 4 - v 4 = 0
    simp [CharTwo.sub_eq_add, add_comm]

private theorem plane_displacements (J : HermitianForm 5 F) (hJ : J.form = 1)
    (v : Fin 5 → F) (hv : v ∈ plane F) :
    ∃ a ∈ shearSubgroup (linearAction J) (plane F), ∃ w, linearAction J a w - w = v := by
  refine ⟨planeSwap J hJ, planeSwap_ambient_shear J hJ, ![0, v 0, 0, v 2, 0], ?_⟩
  rw [planeSwap_apply]
  change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
  ext i
  fin_cases i <;> simp [hv.1, hv.2.1, hv.2.2, CharTwo.neg_eq]

/-- The line shear subgroup, viewed in the ambient PSU group. -/
def ambientLineShears (J : HermitianForm 5 F) := projectiveShearSubgroup J (line F)

/-- The plane shear subgroup, viewed in the ambient PSU group. -/
def ambientPlaneShears (J : HermitianForm 5 F) := projectiveShearSubgroup J (plane F)

/-- The ambient line shears are a two-group. -/
theorem ambientLineShears_isPGroup (J : HermitianForm 5 F) : IsPGroup 2 (ambientLineShears J) :=
  projectiveShearSubgroup_isPGroup J (line F)

/-- The ambient plane shears are a two-group. -/
theorem ambientPlaneShears_isPGroup (J : HermitianForm 5 F) : IsPGroup 2 (ambientPlaneShears J) :=
  projectiveShearSubgroup_isPGroup J (plane F)

/-- The coordinate interchange remains nonidentity after projectivization. -/
theorem ambientLineShears_ne_bot (J : HermitianForm 5 F) (hJ : J.form = 1) :
    ambientLineShears J ≠ ⊥ := by
  intro h
  have hm : project J (lineSwap J hJ) ∈ ambientLineShears J :=
    ⟨_, lineSwap_ambient_shear J hJ, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  exact project_lineSwap_ne_one J hJ hm

/-- The same interchange witnesses nontriviality of the plane shears. -/
theorem ambientPlaneShears_ne_bot (J : HermitianForm 5 F) (hJ : J.form = 1) :
    ambientPlaneShears J ≠ ⊥ := by
  have hs : lineSwap J hJ ∈ shearSubgroup (linearAction J) (plane F) := by
    constructor
    · intro v hv
      rw [lineSwap_apply]
      change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
      ext i
      fin_cases i <;> simp [hv.1]
    · intro v
      exact line_le_plane F ((lineSwap_ambient_shear J hJ).2 v)
  intro h
  have hm : project J (lineSwap J hJ) ∈ ambientPlaneShears J := ⟨_, hs, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  exact project_lineSwap_ne_one J hJ hm

variable [Finite F]

/-- The full line parabolic is the ambient normalizer of the line shears. -/
theorem normalizer_ambientLineShears (J : HermitianForm 5 F) (hJ : J.form = 1) :
    Subgroup.normalizer (ambientLineShears J : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      lineParabolic J :=
  normalizer_projectiveShearSubgroup J (line F) (line_displacements J hJ)

/-- The full plane parabolic is the ambient normalizer of the plane shears. -/
theorem normalizer_ambientPlaneShears (J : HermitianForm 5 F) (hJ : J.form = 1) :
    Subgroup.normalizer (ambientPlaneShears J : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      planeParabolic J :=
  normalizer_projectiveShearSubgroup J (plane F) (plane_displacements J hJ)

/-- The actual projective line parabolic is two-local. -/
theorem lineParabolic_isTwoLocal (J : HermitianForm 5 F) (hJ : J.form = 1) :
    IsTwoLocal (lineParabolic J) :=
  ⟨ambientLineShears J, ambientLineShears_ne_bot J hJ, ambientLineShears_isPGroup J,
    (normalizer_ambientLineShears J hJ).symm⟩

/-- The actual projective plane parabolic is two-local. -/
theorem planeParabolic_isTwoLocal (J : HermitianForm 5 F) (hJ : J.form = 1) :
    IsTwoLocal (planeParabolic J) :=
  ⟨ambientPlaneShears J, ambientPlaneShears_ne_bot J hJ, ambientPlaneShears_isPGroup J,
    (normalizer_ambientPlaneShears J hJ).symm⟩

end Theory.SpecificGroups.UnitaryFive
