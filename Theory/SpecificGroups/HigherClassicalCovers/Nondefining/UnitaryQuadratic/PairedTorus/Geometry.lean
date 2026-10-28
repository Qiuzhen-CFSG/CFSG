module

public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining

/-!
# Reciprocal paired tori in the four-dimensional unitary group

The hyperbolic Gram matrix pairs coordinates 0 with 2 and 1 with 3.
Fixed-field coefficients therefore give diagonal isometries
`diag(a,b,a⁻¹,b⁻¹)`. The even permutation `(0 1)(2 3)` interchanges the
parameters. Only scalar signs can disappear on passage to the actual image
in PGL, so every odd coefficient subgroup embeds faithfully.

Source: the degree-four covering step of Aschbacher–Smith A.2.17, printed
p.39, with perfect-cover conventions I.1.1, printed p.407.
-/

@[expose] public noncomputable section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open OddFourRanks.Defining ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F) (C : Subgroup Fˣ)
variable (hC : ∀ u : C, J.conj (u.val : F) = (u.val : F))

/-- Reciprocal entries on the two hyperbolic pairs. -/
def entries (a : Fin 2 → C) : Fin 4 → C := ![a 0, a 1, (a 0)⁻¹, (a 1)⁻¹]

private theorem entries_det (a : Fin 2 → C) :
    (diagonal (fun i => ((entries C a i).val : F))).det = 1 := by
  rw [det_diagonal]
  simp [entries, Fin.prod_univ_succ, mul_comm, mul_left_comm]

/-- The actual invertible diagonal matrix. -/
def diagonalGL (a : Fin 2 → C) : GL (Fin 4) F :=
  GeneralLinearGroup.mkOfDetNeZero
    (diagonal (fun i => ((entries C a i).val : F)))
    (by rw [entries_det]; exact one_ne_zero)

@[simp] theorem diagonalGL_val (a : Fin 2 → C) :
    (diagonalGL C a).val = diagonal (fun i => ((entries C a i).val : F)) := rfl

include hC in
/-- Fixed coefficients preserve the hyperbolic form, including determinant one. -/
theorem diagonalGL_special (a : Fin 2 → C) :
    diagonalGL C a ∈ (hyperbolicForm J).specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, hyperbolicForm, gram, diagonalGL_val,
        Matrix.mul_apply, Fin.sum_univ_succ, entries, hC, map_inv₀,
        Units.ne_zero, mul_assoc]
  · apply Units.ext
    exact entries_det C a

/-- The paired torus as a matrix homomorphism into SU₄. -/
def special : (Fin 2 → C) →* (hyperbolicForm J).specialSubgroup where
  toFun a := ⟨diagonalGL C a, diagonalGL_special J C hC a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalGL_val, entries]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [entries, mul_comm]

/-- The literal paired torus map into PSU₄ of the hyperbolic form. -/
def projective : (Fin 2 → C) →* ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J) :=
  (project (hyperbolicForm J)).comp (special J C hC)

/-- Projectivization loses only signs, and hence is faithful on odd coefficients. -/
theorem projective_injective [Finite F] (ho : (Nat.card C).Coprime 2) :
    Function.Injective (projective J C hC) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hp : ProjGenLinGroup.mk (diagonalGL C a) = 1 := congrArg Subtype.val ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd (i : Fin 4) : ((entries C a i).val : F) = (u : F) := by
    have hi := congrArg (fun g : GL (Fin 4) F => g.val i i) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonalGL_val] using hi.symm
  have h0 : (a 0).val = u := Units.ext (hd 0)
  have h1 : (a 1).val = u := Units.ext (hd 1)
  have h2 : ((a 0)⁻¹).val = u := Units.ext (hd 2)
  have ha2 : a 0 ^ 2 = 1 := by
    apply Subtype.ext
    change (a 0).val ^ 2 = 1
    have he : (a 0).val⁻¹ = (a 0).val := h2.trans h0.symm
    calc
      _ = (a 0).val⁻¹ * (a 0).val := by rw [pow_two]; exact congrArg (· * (a 0).val) he.symm
      _ = 1 := inv_mul_cancel _
  have ha0 : a 0 = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one ha2))
  have hu1 : u = 1 := h0.symm.trans (congrArg Subtype.val ha0)
  funext i
  fin_cases i
  · exact ha0
  · exact Subtype.ext (h1.trans hu1)

/-- The even permutation interchanging the two hyperbolic pairs. -/
def swapGL : GL (Fin 4) F where
  val := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]
  inv := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The pair swap lies in SU₄, without a determinant correction. -/
theorem swapGL_special : swapGL (F := F) ∈ (hyperbolicForm J).specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapGL, hyperbolicForm, gram, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    simp [swapGL, GeneralLinearGroup.val_det_apply, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Fin.succAbove]

/-- The actual projective pair swap. -/
def swap : ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J) :=
  project (hyperbolicForm J) ⟨swapGL, swapGL_special J⟩

/-- Conjugation by the pair swap interchanges the two parameters. -/
theorem swap_projective (a : Fin 2 → C) :
    swap J * projective J C hC a * (swap J)⁻¹ = projective J C hC ![a 1,a 0] := by
  change project _ _ * project _ _ * (project _ _)⁻¹ = project _ _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change swapGL.val * (diagonalGL C a).val * (swapGL⁻¹).val =
    (diagonalGL C ![a 1,a 0]).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapGL, diagonalGL_val, entries, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]


end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus
