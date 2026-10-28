module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# A projective involution and its full centralizer in PSU₄(3)

The matrix diag(-1,-1,1,1) lies in the identity-form special unitary group
and remains a nonidentity involution in its actual image in PGL. A special
unitary matrix centralizes this projective involution exactly when its matrix
commutes or anticommutes with the representative. Indeed a scalar commutator
must square to one, so it is either 1 or -1. The latter case retains the
interchange of the two eigenspaces, which the ordinary SU centralizer omits.

This supplies a concrete interface for the intrinsic two-core calculation;
no core or involution-conjugacy assertion is assumed or proved here.
Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.3–4 of
`refs/quasithin.pdf`; projective unitary conventions in GLS3, chapter 2.
-/

open Matrix BenderSuzuki.MatrixGroups

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

/-- The two-by-two eigenspace decomposition of a determinant-one involution. -/
def standardInvolutionMatrix : Matrix (Fin 4) (Fin 4) FiniteField.Nine :=
  Matrix.diagonal ![-1, -1, 1, 1]

theorem standardInvolutionMatrix_sq :
    standardInvolutionMatrix * standardInvolutionMatrix = 1 := by decide

def standardInvolutionGL : GL (Fin 4) FiniteField.Nine :=
  ⟨standardInvolutionMatrix, standardInvolutionMatrix,
    standardInvolutionMatrix_sq, standardInvolutionMatrix_sq⟩

/-- The representative is an actual special unitary matrix. -/
def standardInvolutionSU : (form 4).specialSubgroup :=
  ⟨standardInvolutionGL, by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (standardInvolutionMatrix.map star).transpose * 1 * standardInvolutionMatrix = 1
      decide
    · apply Units.ext
      change standardInvolutionMatrix.det = 1
      simp [standardInvolutionMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]⟩

/-- Its image under the defining SU-to-PGL projection. -/
def standardInvolution : Carrier 4 := project 4 standardInvolutionSU

theorem standardInvolutionGL_sq : standardInvolutionGL ^ 2 = 1 := by
  rw [pow_two]
  exact Units.ext standardInvolutionMatrix_sq

theorem standardInvolutionSU_sq : standardInvolutionSU ^ 2 = 1 :=
  Subtype.ext standardInvolutionGL_sq

theorem standardInvolution_sq : standardInvolution ^ 2 = 1 := by
  change project 4 standardInvolutionSU ^ 2 = 1
  rw [← map_pow, standardInvolutionSU_sq, map_one]

theorem standardInvolution_ne_one : standardInvolution ≠ 1 := by
  intro h
  have hk : ProjGenLinGroup.mk standardInvolutionGL = 1 := congrArg Subtype.val h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hk
  obtain ⟨u, hu⟩ := hk
  have h0 := congrArg (fun a : GL (Fin 4) FiniteField.Nine => a.val 0 0) hu
  have h2 := congrArg (fun a : GL (Fin 4) FiniteField.Nine => a.val 2 2) hu
  change (u : FiniteField.Nine) = -1 at h0
  change (u : FiniteField.Nine) = 1 at h2
  have : (-1 : FiniteField.Nine) = 1 := h0.symm.trans h2
  exact (by decide : (-1 : FiniteField.Nine) ≠ 1) this

/-- The scalar quotient does not kill this involution. -/
theorem standardInvolution_orderOf : orderOf standardInvolution = 2 :=
  orderOf_eq_prime standardInvolution_sq standardInvolution_ne_one

/-- The actual centralizer in the projective image, including block interchange. -/
abbrev standardCentralizer := Subgroup.centralizer ({standardInvolution} : Set (Carrier 4))

/-- The full projective centralizer allows both preservation and interchange of the two blocks. -/
theorem project_mem_standardCentralizer_iff (g : (form 4).specialSubgroup) :
    project 4 g ∈ standardCentralizer ↔
      g.val.val * standardInvolutionMatrix = standardInvolutionMatrix * g.val.val ∨
        g.val.val * standardInvolutionMatrix = -(standardInvolutionMatrix * g.val.val) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he : ProjGenLinGroup.mk standardInvolutionGL =
        ProjGenLinGroup.mk (g.val * standardInvolutionGL * g.val⁻¹) := by
      change project 4 g * project 4 standardInvolutionSU =
        project 4 standardInvolutionSU * project 4 g at h
      have h' := congrArg Subtype.val h
      change ProjGenLinGroup.mk g.val * ProjGenLinGroup.mk standardInvolutionGL =
        ProjGenLinGroup.mk standardInvolutionGL * ProjGenLinGroup.mk g.val at h'
      rw [map_mul, map_mul, map_inv, h', mul_inv_cancel_right]
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    have hs : (standardInvolutionGL * GeneralLinearGroup.scalar (Fin 4) u) ^ 2 = 1 := by
      rw [hu]
      change (MulAut.conj g.val standardInvolutionGL) ^ 2 = 1
      rw [← map_pow, standardInvolutionGL_sq, map_one]
    have hcomm : Commute standardInvolutionGL (GeneralLinearGroup.scalar (Fin 4) u) :=
      (GeneralLinearGroup.scalar_commute u standardInvolutionGL).symm
    rw [hcomm.mul_pow, standardInvolutionGL_sq, one_mul, ← map_pow] at hs
    have hu2 : (u.val : FiniteField.Nine) ^ 2 = 1 :=
      congrArg (fun a : GL (Fin 4) FiniteField.Nine => a.val 0 0) hs
    have hm : g.val.val * standardInvolutionMatrix =
        (standardInvolutionMatrix * g.val.val) * Matrix.scalar (Fin 4) u.val := by
      have hh := congrArg (fun a : GL (Fin 4) FiniteField.Nine => a * g.val) hu
      rw [inv_mul_cancel_right] at hh
      rw [mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc] at hh
      exact (congrArg Units.val hh).symm
    rcases sq_eq_one_iff.mp hu2 with hup | hum
    · left
      simpa [hup] using hm
    · right
      simpa [hum, ← Matrix.diagonal_neg, Matrix.diagonal_one] using hm
  · intro h
    apply Subtype.ext
    change ProjGenLinGroup.mk g.val * ProjGenLinGroup.mk standardInvolutionGL =
      ProjGenLinGroup.mk standardInvolutionGL * ProjGenLinGroup.mk g.val
    rw [← map_mul, ← map_mul]
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    rcases h with hp | hm
    · exact ⟨1, by simpa using
        (Units.ext hp : g.val * standardInvolutionGL = standardInvolutionGL * g.val)⟩
    · refine ⟨-1, ?_⟩
      apply Units.ext
      change (g.val.val * standardInvolutionMatrix) * Matrix.scalar (Fin 4) (-1 : FiniteField.Nine) =
        standardInvolutionMatrix * g.val.val
      simp [hm, ← Matrix.diagonal_neg, Matrix.diagonal_one]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
