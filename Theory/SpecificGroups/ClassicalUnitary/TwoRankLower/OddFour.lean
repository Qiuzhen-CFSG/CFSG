module
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
/-!
# An elementary eight in odd-characteristic PSU4

Two determinant-one diagonal sign matrices and a double transposition give
three commuting projective involutions. The single anticommutation is the
scalar minus one; diagonal and off-diagonal entries exclude every other scalar
product. This calculation uses the actual identity Hermitian form and its
literal image in PGL, without a simplicity or order theorem.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.TwoRank.OddFour
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2
private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]
private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]
private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
private def matrix (i : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  ![diagonal ![-1,-1,1,1], diagonal ![-1,1,-1,1],
    !![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0]] i

private theorem matrix_square (i : Fin 3) : matrix (F:=F) i * matrix i = 1 := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrix,Matrix.mul_apply,Fin.sum_univ_succ]
private theorem matrix_det (i : Fin 3) : (matrix (F:=F) i).det = 1 := by
  fin_cases i
  · simp [matrix,det_diagonal,Fin.prod_univ_succ]
  · simp [matrix,det_diagonal,Fin.prod_univ_succ]
  · norm_num [matrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]
    change (1:F) * 1 + -(0 * 0) = 1
    simp

private def actor (i : Fin 3) : (OddFundamental.form σ hσ 4).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (matrix i) (by rw [matrix_det];exact one_ne_zero),by
    constructor
    · change (OddFundamental.form σ hσ 4).conjTranspose (matrix i) * 1 * matrix i = 1
      rw [mul_one]
      have ha : (OddFundamental.form σ hσ 4).conjTranspose (matrix i) = matrix i := by
        ext j k
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          simp [matrix,OddFundamental.form,HermitianForm.conjTranspose]
      rw [ha,matrix_square]
    · exact Units.ext (matrix_det i)⟩

private def image (i : Fin 3) : ProjectiveSpecialUnitaryMatrixGroup (OddFundamental.form σ hσ 4) := ProjectiveKernel.project (OddFundamental.form σ hσ 4) (actor σ hσ i)
private theorem actor_square (i : Fin 3) : actor σ hσ i ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change matrix (F:=F) i ^ 2 = 1
  rw [pow_two]
  exact matrix_square (F:=F) i
private theorem image_square (i : Fin 3) : image σ hσ i ^ 2 = 1 := by
  rw [image,←map_pow,actor_square,map_one]
private theorem commute_zero_one : Commute (image σ hσ 0) (image σ hσ 1) := by
  apply Subtype.ext
  change ProjGenLinGroup.mk ((actor σ hσ 0).val * (actor σ hσ 1).val) =
    ProjGenLinGroup.mk ((actor σ hσ 1).val * (actor σ hσ 0).val)
  congr 1
  apply Units.ext
  change diagonal _ * diagonal _ = diagonal _ * diagonal _
  simp only [diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _
private theorem commute_zero_two : Commute (image σ hσ 0) (image σ hσ 2) := by
  apply Subtype.ext
  change ProjGenLinGroup.mk ((actor σ hσ 0).val * (actor σ hσ 2).val) =
    ProjGenLinGroup.mk ((actor σ hσ 2).val * (actor σ hσ 0).val)
  congr 1
  apply Units.ext
  change diagonal _ * matrix (F:=F) 2 = matrix 2 * diagonal _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,diagonal_mul,mul_diagonal]
private theorem commute_one_two : Commute (image σ hσ 1) (image σ hσ 2) := by
  apply Subtype.ext
  change ProjGenLinGroup.mk ((actor σ hσ 1).val * (actor σ hσ 2).val) =
    ProjGenLinGroup.mk ((actor σ hσ 2).val * (actor σ hσ 1).val)
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨(-1:Fˣ), ?_⟩
  apply Units.ext
  change (diagonal _ * matrix (F:=F) 2) * Matrix.scalar _ (-1) = matrix 2 * diagonal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.scalar,diagonal_mul,mul_diagonal]

private def embedding : E →* ProjectiveSpecialUnitaryMatrixGroup (OddFundamental.form σ hσ 4) :=
  tripleHom (image σ hσ 0) (image σ hσ 1) (image σ hσ 2)
    (image_square σ hσ 0) (image_square σ hσ 1) (image_square σ hσ 2)
    (commute_zero_one σ hσ) (commute_zero_two σ hσ) (commute_one_two σ hσ)
private def raw (x : E) := (if x.1.1=1 then 1 else actor σ hσ 0) *
  (if x.1.2=1 then 1 else actor σ hσ 1) * (if x.2=1 then 1 else actor σ hσ 2)
private theorem embedding_raw (x : E) : embedding σ hσ x =
    ProjectiveKernel.project _ (raw σ hσ x) := by
  simp only [embedding,tripleHom,MonoidHom.noncommCoprod_apply,binaryHom,
    MonoidHom.coe_mk,OneHom.coe_mk,raw,map_mul]
  split_ifs <;> simp [image]
private theorem embedding_injective (hF : (2:F) ≠ 0) : Function.Injective (embedding σ hσ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [embedding_raw] at hx
  have hp : ProjGenLinGroup.mk (raw σ hσ x).val = 1 := congrArg Subtype.val hx
  rw [ProjGenLinGroup.mk_eq_one,GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u,hu⟩ := hp
  have h00 := congrArg (fun M : GL (Fin 4) F => M.val 0 0) hu
  have h11 := congrArg (fun M : GL (Fin 4) F => M.val 1 1) hu
  have h22 := congrArg (fun M : GL (Fin 4) F => M.val 2 2) hu
  have h33 := congrArg (fun M : GL (Fin 4) F => M.val 3 3) hu
  have h01 := congrArg (fun M : GL (Fin 4) F => M.val 0 1) hu
  have hn : (-1:Fˣ) ≠ 1 := by
    intro h
    have he : (-1:F) = 1 := congrArg Units.val h
    apply hF
    linear_combination -he
  by_cases ha : x.1.1=1 <;> by_cases hb : x.1.2=1 <;> by_cases hc : x.2=1
  all_goals simp [raw,ha,hb,hc,actor,matrix,GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply,Fin.sum_univ_succ] at h00 h11 h22 h33 h01
  · exact Prod.ext (Prod.ext ha hb) hc
  all_goals first | exact (hn (h00.symm.trans h33)).elim |
    exact (hn (h11.symm.trans h33)).elim

/-- The identity-form PSU4 contains an elementary eight whenever the characteristic is odd. -/
theorem three_le [Finite F] (hF : (2:F) ≠ 0) :
    3 ≤ primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup (OddFundamental.form σ hσ 4)) := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (OddFundamental.form σ hσ 4)) :=
    Finite.of_surjective (ProjectiveKernel.project _) (ProjectiveKernel.project_surjective _)
  apply primeRank_ge_of_elementary_embedding (f := embedding σ hσ)
  · exact (by decide +kernel : ∀x:E,x^2=1)
  · simp [E,C2]
  · exact embedding_injective σ hσ hF
end Theory.SpecificGroups.ClassicalUnitary.TwoRank.OddFour
