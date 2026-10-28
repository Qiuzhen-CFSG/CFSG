module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.Tactic.FinCases

/-!
# Three defining-characteristic directions in PSU₄

For the hyperbolic Hermitian form, upper shears with a symmetric two-by-two
block multiplied by a nonzero trace-zero scalar give an embedded copy of the
additive prime field cubed. The diagonal entries of every shear are one, so
projectivization remains injective. Two orthonormal bases give an actual
projective equivalence to any original Hermitian form with prime Frobenius.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39, the dimension-four ordinary defining-rank exclusion.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
open ProjectiveKernel UnitaryFourThree
variable {F : Type*} [Field F]

/-- A pair of hyperbolic planes. -/
def gram : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

private theorem gram_sq : gram (F := F) * gram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The hyperbolic form uses the original field involution. -/
def hyperbolicForm (J : HermitianForm 4 F) : HermitianForm 4 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := gram
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [gram]
  form_nondegenerate := by
    have h := congrArg Matrix.det (gram_sq (F := F))
    rw [det_mul, det_one] at h
    exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

/-- A symmetric upper block, with its three entries free. -/
def shearMatrix (v : Fin 3 → F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,v 0,v 1; 0,1,v 1,v 2; 0,0,1,0; 0,0,0,1]

private theorem shearMatrix_zero : shearMatrix (0 : Fin 3 → F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem shearMatrix_add (v w : Fin 3 → F) :
    shearMatrix (v + w) = shearMatrix v * shearMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem shearMatrix_det (v : Fin 3 → F) : (shearMatrix v).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [shearMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [shearMatrix]

variable (J : HermitianForm 4 F) {r : ℕ} [CharP F r]

private theorem conj_cast (a : ZMod r) : J.conj (a.cast : F) = a.cast := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  simp

/-- A fixed nonzero trace-zero scalar multiplies the symmetric prime-field block. -/
def parameters (α : F) (v : Fin 3 → ZMod r) : Fin 3 → F := fun i => α * (v i).cast

private theorem shear_unitary (α : F) (hα : J.conj α = -α) (v : Fin 3 → ZMod r) :
    (hyperbolicForm J).conjTranspose (shearMatrix (parameters α v)) * gram *
      shearMatrix (parameters α v) = gram := by
  have hv (i : Fin 3) : J.conj (parameters α v i) = -(parameters α v i) := by
    simp only [parameters, map_mul, hα, conj_cast, neg_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicForm, gram, shearMatrix, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, hv]

/-- The shears as an actual homomorphism to SU₄ of the hyperbolic form. -/
def shearSpecial (α : F) (hα : J.conj α = -α) :
    Multiplicative (Fin 3 → ZMod r) →* (hyperbolicForm J).specialSubgroup where
  toFun v := ⟨GeneralLinearGroup.mkOfDetNeZero (shearMatrix (parameters α v.toAdd))
    (by rw [shearMatrix_det]; exact one_ne_zero),
    by exact shear_unitary J α hα v.toAdd, by exact Units.ext (shearMatrix_det _)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change shearMatrix (parameters α (0 : Fin 3 → ZMod r)) = 1
    have h : parameters α (0 : Fin 3 → ZMod r) = 0 := by ext i; simp [parameters]
    rw [h, shearMatrix_zero]
  map_mul' v w := by
    apply Subtype.ext
    apply Units.ext
    change shearMatrix (parameters α (v.toAdd + w.toAdd)) = _
    have h : parameters α (v.toAdd + w.toAdd) = parameters α v.toAdd + parameters α w.toAdd := by
      ext i
      simp [parameters, mul_add]
    rw [h, shearMatrix_add]
    rfl

/-- The shears in the actual projective image, retaining the scalar quotient. -/
def projectiveShear (α : F) (hα : J.conj α = -α) :
    Multiplicative (Fin 3 → ZMod r) →* ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J) :=
  (project (hyperbolicForm J)).comp (shearSpecial J α hα)

theorem projectiveShear_injective (α : F) (hα : J.conj α = -α) (hα0 : α ≠ 0) :
    Function.Injective (projectiveShear (r := r) J α hα) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hp : ProjGenLinGroup.mk (shearSpecial (r := r) J α hα v).val = 1 :=
    congrArg Subtype.val hv
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hentry (i j : Fin 4) := congrArg (fun g : GL (Fin 4) F => g.val i j) hu
  have hz (i : Fin 3) : parameters α v.toAdd i = 0 := by
    fin_cases i
    · simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, shearSpecial, shearMatrix]
        using (hentry 0 2).symm
    · simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, shearSpecial, shearMatrix]
        using (hentry 0 3).symm
    · simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, shearSpecial, shearMatrix]
        using (hentry 1 3).symm
  change v.toAdd = 0
  funext i
  apply ZMod.castHom_injective F
  change (v.toAdd i).cast = ((0 : ZMod r).cast : F)
  simpa using (mul_eq_zero.mp (hz i)).resolve_left hα0

variable [Fact r.Prime]

/-- Quadratic prime Frobenius is nontrivial, hence supplies a nonzero trace-zero scalar. -/
theorem exists_trace_zero [Finite F] (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r) :
    ∃ α : F, α ≠ 0 ∧ J.conj α = -α := by
  have hn : ∃ x : F, J.conj x ≠ x := by
    by_contra! h
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val, invFun := fun x => ⟨x, h x⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [J.card_fixed_of_prime_frobenius hconj, hc] at he
    have hr := (Fact.out : r.Prime).two_le
    nlinarith
  obtain ⟨x, hx⟩ := hn
  refine ⟨x - J.conj x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, J.conj_involutive, neg_sub]

/-- The literal projective equivalence from two orthonormal bases. -/
theorem exists_hyperbolic_equiv [Finite F] (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨P, hP⟩ := J.exists_orthonormal_basis_of_prime_frobenius hconj hc
  obtain ⟨Q, hQ⟩ := (hyperbolicForm J).exists_orthonormal_basis_of_prime_frobenius hconj hc
  exact ⟨(projectiveBasisEquiv (hyperbolicForm J) Q hQ).trans
    (projectiveBasisEquiv J P hP).symm⟩

/-- Three independent additive prime-field directions in the original PSU₄. -/
theorem exists_defining_embedding [Finite F] (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r) :
    ∃ f : Multiplicative (Fin 3 → ZMod r) →* ProjectiveSpecialUnitaryMatrixGroup J,
      Function.Injective f := by
  obtain ⟨α, hα0, hα⟩ := exists_trace_zero J hc hconj
  obtain ⟨e⟩ := exists_hyperbolic_equiv J hc hconj
  exact ⟨e.toMonoidHom.comp (projectiveShear J α hα),
    e.injective.comp (projectiveShear_injective J α hα hα0)⟩

/-- The ordinary defining rank exceeds two. -/
theorem three_le_primeRank [Finite F] (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r) :
    3 ≤ primeRank r (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project J) (project_surjective J)
  obtain ⟨f, hf⟩ := exists_defining_embedding J hc hconj
  refine primeRank_ge_of_elementary_embedding ?_ ?_ f hf
  · intro v
    change r • v.toAdd = 0
    ext i
    simp [nsmul_eq_mul]
  · change Nat.card (Fin 3 → ZMod r) = _
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card]

end Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
