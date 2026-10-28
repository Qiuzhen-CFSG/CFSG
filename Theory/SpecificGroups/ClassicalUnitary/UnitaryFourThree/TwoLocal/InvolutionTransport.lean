module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.ScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport.LinearEigenbasis
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport.UnitaryEigenbasis

/-!
# Scalar reduction and full-centralizer transport in PSU₄(3)

Conjugation by a full unitary matrix preserves the actual special-unitary
image in PGL. It therefore transports full projective centralizers, retaining
both commuting and anticommuting lifts of the standard involution.

The square of an SU lift of a projective involution is a fourth-root scalar.
Every such scalar has a square root in the field of nine elements, so a scalar
multiple of the lift is an ordinary linear involution. Given a trace-zero
linear eigenbasis with two negative and two positive eigenvectors, its
determinant forces the rescaling scalar to belong to SU. Thus the rescaled
lift has exactly the original projective image. A unitary normalization of
the eigenbasis then supplies the centralizer equivalence.

The final theorem supplies the proved linear eigenbasis and Hermitian
normalization constructions, obtaining transport from the trace hypothesis
alone. The trace hypothesis itself belongs to the separate
involution-centralizer calculation.

Source: Aschbacher–Smith, condition E and Theorem 0.1.2(4), printed pp.3–4
and 481–482 of `refs/quasithin.pdf`; GLS3, chapter 2, §2.7, for the actual
SU image in PGL and full-unitary conjugation conventions.
-/

open Matrix BenderSuzuki.MatrixGroups

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

private theorem unitary_conj_special_iff (C : (form 4).unitarySubgroup)
    (B : GL (Fin 4) FiniteField.Nine) :
    C.val * B * C.val⁻¹ ∈ (form 4).specialSubgroup ↔ B ∈ (form 4).specialSubgroup :=
  special_conjugate_iff (form 4) C.val B
    ((HermitianForm.mem_unitarySubgroup_iff _ _).mp C.property)

private theorem projective_unitary_conj_mem (C : (form 4).unitarySubgroup)
    (x : ProjGenLinGroup (Fin 4) FiniteField.Nine) :
    MulAut.conj (ProjGenLinGroup.mk C.val) x ∈ ProjectiveSpecialUnitaryMatrixGroup (form 4) ↔
      x ∈ ProjectiveSpecialUnitaryMatrixGroup (form 4) := by
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨C.val⁻¹ * a * C.val, ?_, ?_⟩
    · apply (unitary_conj_special_iff C _).mp
      rw [show C.val * (C.val⁻¹ * a * C.val) * C.val⁻¹ = a by group]
      exact ha
    · change ProjGenLinGroup.mk a =
        ProjGenLinGroup.mk C.val * x * (ProjGenLinGroup.mk C.val)⁻¹ at hax
      simp only [map_mul, map_inv]
      rw [hax]
      group
  · rintro ⟨a, ha, rfl⟩
    exact ⟨C.val * a * C.val⁻¹, (unitary_conj_special_iff C a).mpr ha,
      by simp only [map_mul, map_inv, MulAut.conj_apply]⟩

/-- Conjugation by a full unitary matrix acts on the actual SU image in PGL. -/
def projectiveUnitaryConj (C : (form 4).unitarySubgroup) : MulAut (Carrier 4) where
  toFun x := ⟨MulAut.conj (ProjGenLinGroup.mk C.val) x.val,
    (projective_unitary_conj_mem C x.val).mpr x.property⟩
  invFun x := ⟨(MulAut.conj (ProjGenLinGroup.mk C.val)).symm x.val,
    (projective_unitary_conj_mem C _).mp (by simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext ((MulAut.conj _).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((MulAut.conj _).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((MulAut.conj _).map_mul x.val y.val)

theorem projectiveUnitaryConj_apply (C : (form 4).unitarySubgroup) (z : Carrier 4) :
    (projectiveUnitaryConj C z).val =
      ProjGenLinGroup.mk C.val * z.val * (ProjGenLinGroup.mk C.val)⁻¹ := by rfl

private def centralizerTransport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({e x} : Set H) where
  toFun y := ⟨e y, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

/-- A unitary conjugator transports the full projective centralizer. -/
def centralizerEquivOfUnitaryConjugator (A : (form 4).specialSubgroup)
    (C : (form 4).unitarySubgroup)
    (hC : C.val * standardInvolutionGL * C.val⁻¹ = A.val) :
    Subgroup.centralizer ({project 4 A} : Set (Carrier 4)) ≃* standardCentralizer := by
  have he : projectiveUnitaryConj C standardInvolution = project 4 A := by
    apply Subtype.ext
    rw [projectiveUnitaryConj_apply]
    change ProjGenLinGroup.mk C.val * ProjGenLinGroup.mk standardInvolutionGL *
      (ProjGenLinGroup.mk C.val)⁻¹ = ProjGenLinGroup.mk A.val
    rw [← map_inv, ← map_mul, ← map_mul, hC]
  exact (centralizerTransport (projectiveUnitaryConj C) standardInvolution |>.trans
    (MulEquiv.subgroupCongr (congrArg (fun z : Carrier 4 =>
      Subgroup.centralizer ({z} : Set (Carrier 4))) he))).symm

/-- The square of a lift of a projective involution is a fourth-root scalar. -/
theorem project_square_scalar (g : (form 4).specialSubgroup)
    (hg : (project 4 g) ^ 2 = 1) :
    ∃ u : FiniteField.Nineˣ, u ^ 4 = 1 ∧ g.val ^ 2 = GeneralLinearGroup.scalar (Fin 4) u := by
  have hk : ProjGenLinGroup.mk (g.val ^ 2) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hk
  obtain ⟨u, hu⟩ := hk
  refine ⟨u, ?_, hu.symm⟩
  apply (IsotropicStabilizers.scalar_mem_specialSubgroup_iff (form 4) (form_conj_cube 4) u).mp
  rw [hu]
  exact (form 4).specialSubgroup.pow_mem g.property 2

/-- Fourth roots in the field of nine elements have square roots. -/
theorem fourth_root_has_square_root (u : FiniteField.Nineˣ) (hu : u ^ 4 = 1) :
    ∃ a : FiniteField.Nineˣ, a ^ 2 = u := by
  have h : ∀ x : FiniteField.Nine, x ^ 4 = 1 → ∃ y : FiniteField.Nine, y ^ 2 = x := by decide
  obtain ⟨a, ha⟩ := h u (congrArg Units.val hu)
  have ha0 : a ≠ 0 := by
    intro hz
    exact u.ne_zero (by simpa [hz] using ha.symm)
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

/-- Rescale a projective involution lift to an ordinary linear involution.
The rescaling is not yet asserted to lie in SU. -/
theorem exists_involutive_scalar_multiple (g : (form 4).specialSubgroup)
    (hg : (project 4 g) ^ 2 = 1) :
    ∃ a : FiniteField.Nineˣ, (GeneralLinearGroup.scalar (Fin 4) a * g.val) ^ 2 = 1 := by
  obtain ⟨u, hu, hgu⟩ := project_square_scalar g hg
  obtain ⟨a, ha⟩ := fourth_root_has_square_root u⁻¹ (by rw [inv_pow, hu, inv_one])
  refine ⟨a, ?_⟩
  have hc : Commute (GeneralLinearGroup.scalar (Fin 4) a) g.val :=
    GeneralLinearGroup.scalar_commute a g.val
  rw [hc.mul_pow, ← map_pow, ha, hgu,
    ← map_mul, inv_mul_cancel, map_one]

/-- Linear two-plus-two conjugacy forces the rescaling scalar to be an allowed
SU scalar. Consequently the resulting ordinary involution has exactly the same
image in PGL as the original lift. -/
theorem exists_special_lift_of_linear_eigenbases
    (hlinear : ∀ M : GL (Fin 4) FiniteField.Nine, M ^ 2 = 1 → Matrix.trace M.val = 0 →
      ∃ P : GL (Fin 4) FiniteField.Nine,
        P * standardInvolutionGL * P⁻¹ = M)
    (g : (form 4).specialSubgroup) (hsq : (project 4 g) ^ 2 = 1)
    (htrace : Matrix.trace g.val.val = 0) :
    ∃ A : (form 4).specialSubgroup, project 4 A = project 4 g ∧
      ∃ P : GL (Fin 4) FiniteField.Nine,
        P * standardInvolutionGL * P⁻¹ = A.val := by
  obtain ⟨a, ha⟩ := exists_involutive_scalar_multiple g hsq
  let M := GeneralLinearGroup.scalar (Fin 4) a * g.val
  have hMt : Matrix.trace M.val = 0 := by
    change Matrix.trace (Matrix.scalar (Fin 4) a.val * g.val.val) = 0
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul,
      htrace, smul_zero]
  obtain ⟨P, hP⟩ := hlinear M ha hMt
  have hgd : GeneralLinearGroup.det g.val = 1 :=
    ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.2
  have hDd : GeneralLinearGroup.det standardInvolutionGL = 1 :=
    ((form 4).mem_specialSubgroup_iff standardInvolutionGL).mp standardInvolutionSU.property |>.2
  have ha4 : a ^ 4 = 1 := by
    have hd := congrArg GeneralLinearGroup.det hP
    simpa only [M, map_mul, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hgd, hDd, mul_one, mul_inv_cancel] using hd.symm
  have hscalar : GeneralLinearGroup.scalar (Fin 4) a ∈ (form 4).specialSubgroup :=
    (IsotropicStabilizers.scalar_mem_specialSubgroup_iff (form 4) (form_conj_cube 4) a).mpr ha4
  let A : (form 4).specialSubgroup := ⟨M, (form 4).specialSubgroup.mul_mem hscalar g.property⟩
  refine ⟨A, ?_, P, hP⟩
  apply Subtype.ext
  change ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 4) a * g.val) =
    ProjGenLinGroup.mk g.val
  rw [map_mul]
  have hk : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 4) a) = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨a, rfl⟩
  rw [hk, one_mul]

/-- Assembly of the scalar-kernel, linear-eigenbasis and Hermitian-normalization
steps, retaining the two geometric inputs as a reusable conditional interface. -/
theorem centralizer_models_of_eigenbasis_inputs
    (htrace : ∀ g : (form 4).specialSubgroup,
      project 4 g ≠ 1 → (project 4 g) ^ 2 = 1 → Matrix.trace g.val.val = 0)
    (hlinear : ∀ M : GL (Fin 4) FiniteField.Nine, M ^ 2 = 1 → Matrix.trace M.val = 0 →
      ∃ P : GL (Fin 4) FiniteField.Nine,
        P * standardInvolutionGL * P⁻¹ = M)
    (hnormalize : ∀ (A : (form 4).specialSubgroup) (P : GL (Fin 4) FiniteField.Nine),
      P * standardInvolutionGL * P⁻¹ = A.val →
        ∃ C : (form 4).unitarySubgroup,
          C.val * standardInvolutionGL * C.val⁻¹ = A.val) :
    ∀ z : Carrier 4, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set (Carrier 4)) ≃* standardCentralizer) := by
  intro z hz
  obtain ⟨g, rfl⟩ := project_surjective 4 z
  have hs : (project 4 g) ^ 2 = 1 := hz ▸ pow_orderOf_eq_one (project 4 g)
  have hn : project 4 g ≠ 1 := by
    intro he
    simp only [he, orderOf_one] at hz
    omega
  obtain ⟨A, hA, P, hP⟩ := exists_special_lift_of_linear_eigenbases hlinear g hs (htrace g hn hs)
  obtain ⟨C, hC⟩ := hnormalize A P hP
  rw [← hA]
  exact ⟨centralizerEquivOfUnitaryConjugator A C hC⟩

/-- Under the projective involution-lift trace hypothesis, every involution
centralizer in the actual PSU₄(3) image is isomorphic to the full centralizer
of `diag(-1,-1,1,1)`. The linear eigenbasis and its unitary normalization are
constructed, and the equivalence retains the anticommuting projective lifts. -/
theorem centralizer_models_of_trace_zero
    (htrace : ∀ g : (form 4).specialSubgroup,
      project 4 g ≠ 1 → (project 4 g) ^ 2 = 1 → Matrix.trace g.val.val = 0) :
    ∀ z : Carrier 4, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set (Carrier 4)) ≃* standardCentralizer) :=
  centralizer_models_of_eigenbasis_inputs htrace
    exists_linear_conjugator_of_trace_zero exists_unitary_conjugator_of_linear

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
