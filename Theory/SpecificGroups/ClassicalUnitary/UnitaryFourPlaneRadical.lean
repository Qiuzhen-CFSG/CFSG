module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.Model
public import Theory.ElementaryAbelian.Basic
import Mathlib.Algebra.CharP.Two

/-!
# The Hermitian radical of the unitary-four plane local

For the antidiagonal Hermitian form in characteristic two, the kernel of
restriction to the invariant plane is exactly the additive group of Hermitian
2-by-2 matrices. The parametrization sends X to the upper unipotent with block
X*S, where S reverses the two coordinates. The unitary equation forces the
opposite diagonal block to be identity and the remaining block to be Hermitian.
Thus the entire kernel is elementary abelian, with explicit mutually inverse
maps and a literal matrix multiplication formula.

Source: Aschbacher--Smith, F.1.12(I)(6), printed pp.263–264 of
`refs/quasithin.pdf`. This module establishes the restriction kernel; identifying
it with the two-core and proving the quotient and conjugation formulas are
separate obligations.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
open Representation.OrthogonalFourMinus
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
variable (F : Type*) [Field F] (σ : F ≃+* F)

/-- Additive Hermitian matrices for the specified involution. -/
def hermitianMatrices : AddSubgroup (Mat F) where
  carrier := {X | adjoint σ X = X}
  zero_mem' := by ext i j; exact map_zero σ
  add_mem' := by intro X Y hX hY; change adjoint σ (X + Y) = X + Y; rw [adjoint_add, hX, hY]
  neg_mem' := by
    intro X hX
    ext i j
    change σ (-X j i) = -X i j
    rw [map_neg, show σ (X j i) = X i j from congrFun (congrFun hX i) j]

/-- In block notation this is `[[I, X*S], [0, I]]`, with `S` reversing two coordinates. -/
def unipotentMatrix (X : Mat F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,X 0 1,X 0 0; 0,1,X 1 1,X 1 0; 0,0,1,0; 0,0,0,1]

theorem unipotentMatrix_zero : unipotentMatrix F 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem unipotentMatrix_add (X Y : Mat F) :
    unipotentMatrix F (X + Y) = unipotentMatrix F X * unipotentMatrix F Y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [unipotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

theorem unipotentMatrix_injective : Function.Injective (unipotentMatrix F) := by
  intro X Y h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M => M 0 3) h
  · exact congrArg (fun M => M 0 2) h
  · exact congrArg (fun M => M 1 3) h
  · exact congrArg (fun M => M 1 2) h

theorem unipotentMatrix_det (X : Mat F) : (unipotentMatrix F X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [unipotentMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [unipotentMatrix]

variable (hσ : Function.Involutive σ) [CharP F 2]

theorem unipotentMatrix_unitary (X : hermitianMatrices F σ) :
    (form F σ hσ).conjTranspose (unipotentMatrix F X.val) * gram F *
      unipotentMatrix F X.val = gram F := by
  have hx (i j : Fin 2) : σ (X.val j i) = X.val i j := congrFun (congrFun X.property i) j
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form, gram, unipotentMatrix, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, hx, CharTwo.add_self_eq_zero]

/-- The Hermitian unipotent, as an actual special unitary element. -/
def unipotentSU (X : hermitianMatrices F σ) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (unipotentMatrix F X.val)
    (by rw [unipotentMatrix_det]; exact one_ne_zero),
   unipotentMatrix_unitary F σ hσ X, Units.ext (unipotentMatrix_det F X.val)⟩

variable [Finite F]

theorem unipotentSU_mem_local (X : hermitianMatrices F σ) :
    unipotentSU F σ hσ X ∈ localFactor F (form F σ hσ) := by
  apply (mem_localFactor F _ _).mpr
  refine ⟨?_, ?_⟩
  · rw [mem_planeParabolicSU]
    simp [unipotentSU, unipotentMatrix]
  · simp [restrictionMatrix, unipotentSU, unipotentMatrix, Matrix.det_fin_two]

/-- The restriction kernel inside the embedded determinant-one local factor. -/
def radical : Subgroup (localFactor F (form F σ hσ)) :=
  (factorRestriction F (form F σ hσ)).ker

instance radical_normal : (radical F σ hσ).Normal :=
  inferInstanceAs (factorRestriction F (form F σ hσ)).ker.Normal

omit [CharP F 2] in
/-- Entry formula for restriction on the embedded local group. -/
theorem factorRestriction_val (g : localFactor F (form F σ hσ)) :
    (factorRestriction F (form F σ hσ) g).val =
      !![g.val.val.val 0 0,g.val.val.val 0 1;g.val.val.val 1 0,g.val.val.val 1 1] := by
  obtain ⟨g,rfl⟩ := (localFactorEquiv F (form F σ hσ)).surjective g
  simp only [factorRestriction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rfl

omit [CharP F 2] in
theorem mem_radical (g : localFactor F (form F σ hσ)) : g ∈ radical F σ hσ ↔
    g.val.val.val 0 0 = 1 ∧ g.val.val.val 0 1 = 0 ∧
    g.val.val.val 1 0 = 0 ∧ g.val.val.val 1 1 = 1 := by
  change factorRestriction F (form F σ hσ) g = 1 ↔ _
  constructor
  · intro h
    have h := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val) h
    rw [factorRestriction_val] at h
    exact ⟨congrArg (fun M => M 0 0) h, congrArg (fun M => M 0 1) h,
      congrArg (fun M => M 1 0) h, congrArg (fun M => M 1 1) h⟩
  · rintro ⟨h00,h01,h10,h11⟩
    apply Subtype.ext
    rw [factorRestriction_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00,h01,h10,h11]

/-- Additive Hermitian matrices map multiplicatively into the entire kernel's carrier. -/
def unipotent : Multiplicative (hermitianMatrices F σ) →* radical F σ hσ where
  toFun X := ⟨⟨unipotentSU F σ hσ X.toAdd, unipotentSU_mem_local F σ hσ X.toAdd⟩, by
    rw [mem_radical]; simp [unipotentSU, unipotentMatrix]⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact unipotentMatrix_zero F
  map_mul' X Y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact unipotentMatrix_add F X.toAdd.val Y.toAdd.val

theorem unipotent_injective : Function.Injective (unipotent F σ hσ) := by
  intro X Y h
  change X.toAdd = Y.toAdd
  apply Subtype.ext
  apply unipotentMatrix_injective F
  exact congrArg (fun a : radical F σ hσ => a.val.val.val.val) h


omit [CharP F 2] in
/-- Unitarity forces the opposite diagonal block of a kernel element to be identity. -/
theorem radical_lower_block (g : radical F σ hσ) :
    g.val.val.val.val 2 2 = 1 ∧ g.val.val.val.val 2 3 = 0 ∧
    g.val.val.val.val 3 2 = 0 ∧ g.val.val.val.val 3 3 = 1 := by
  obtain ⟨h00,h01,h10,h11⟩ := (mem_radical F σ hσ g.val).mp g.property
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F _ g.val.val).mp
    (local_le_planeParabolic F _ g.val.property)
  have hu := g.val.val.property.1
  change (form F σ hσ).conjTranspose g.val.val.val.val * gram F *
    g.val.val.val.val = gram F at hu
  have he (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j) hu
  have h12 := he 1 2
  have h13 := he 1 3
  have h02 := he 0 2
  have h03 := he 0 3
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h00,h01,h10,h11,h20,h30,h21,h31] at h12 h13 h02 h03
  exact ⟨h12,h13,h02,h03⟩

/-- Extract `X` from the upper-right block `X*S` of an arbitrary kernel element. -/
def coordinatesOfRadical (g : radical F σ hσ) : hermitianMatrices F σ :=
  ⟨!![g.val.val.val.val 0 3,g.val.val.val.val 0 2;
       g.val.val.val.val 1 3,g.val.val.val.val 1 2], by
    obtain ⟨h22,h23,h32,h33⟩ := radical_lower_block F σ hσ g
    have hu := g.val.val.property.1
    change (form F σ hσ).conjTranspose g.val.val.val.val * gram F *
      g.val.val.val.val = gram F at hu
    have he (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j) hu
    have he22 := he 2 2
    have he23 := he 2 3
    have he32 := he 3 2
    have he33 := he 3 3
    simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, h22,h23,h32,h33] at he22 he23 he32 he33
    ext i j
    fin_cases i <;> fin_cases j
    · exact (CharTwo.add_eq_zero.mp he33).symm
    · exact (CharTwo.add_eq_zero.mp he32).symm
    · exact (CharTwo.add_eq_zero.mp he23).symm
    · exact (CharTwo.add_eq_zero.mp he22).symm⟩

@[simp] theorem coordinatesOfRadical_unipotent (X : Multiplicative (hermitianMatrices F σ)) :
    coordinatesOfRadical F σ hσ (unipotent F σ hσ X) = X.toAdd := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Exhaustiveness of the Hermitian parametrization. -/
theorem unipotent_coordinatesOfRadical (g : radical F σ hσ) :
    unipotent F σ hσ (Multiplicative.ofAdd (coordinatesOfRadical F σ hσ g)) = g := by
  obtain ⟨h00,h01,h10,h11⟩ := (mem_radical F σ hσ g.val).mp g.property
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F _ g.val.val).mp
    (local_le_planeParabolic F _ g.val.property)
  obtain ⟨h22,h23,h32,h33⟩ := radical_lower_block F σ hσ g
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, unipotentSU, unipotentMatrix, coordinatesOfRadical,
      h00,h01,h10,h11,h20,h30,h21,h31,h22,h23,h32,h33]

/-- The entire restriction kernel is the additive Hermitian matrix group. -/
def radicalEquiv : Multiplicative (hermitianMatrices F σ) ≃* radical F σ hσ :=
  MulEquiv.ofBijective (unipotent F σ hσ)
    ⟨unipotent_injective F σ hσ, fun g =>
      ⟨Multiplicative.ofAdd (coordinatesOfRadical F σ hσ g),
        unipotent_coordinatesOfRadical F σ hσ g⟩⟩

@[simp] theorem radicalEquiv_apply (X : Multiplicative (hermitianMatrices F σ)) :
    radicalEquiv F σ hσ X = unipotent F σ hσ X := rfl

/-- The restriction kernel is abelian. -/
theorem radical_mul_comm (g h : radical F σ hσ) : g * h = h * g := by
  obtain ⟨X,rfl⟩ := (radicalEquiv F σ hσ).surjective g
  obtain ⟨Y,rfl⟩ := (radicalEquiv F σ hσ).surjective h
  rw [← map_mul, ← map_mul, mul_comm]

/-- Every element of the restriction kernel has square one. -/
theorem radical_sq (g : radical F σ hσ) : g ^ 2 = 1 := by
  obtain ⟨X,rfl⟩ := (radicalEquiv F σ hσ).surjective g
  rw [← map_pow, ← map_one (radicalEquiv F σ hσ)]
  congr 1
  rw [pow_two]
  change (X * X).toAdd = (1 : Multiplicative (hermitianMatrices F σ)).toAdd
  apply Subtype.ext
  change X.toAdd.val + X.toAdd.val = 0
  ext i j
  exact CharTwo.add_self_eq_zero _

instance radical_elementaryAbelian : IsElementaryAbelian 2 (radical F σ hσ) where
  is_comm.comm := radical_mul_comm F σ hσ
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (radical_sq F σ hσ)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
