module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.Setup
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Action

/-!
# Coordinates for the full plane-parabolic action

The Hermitian radical is the sum of its two fixed-field diagonal coordinates
and one matrix-field off-diagonal coordinate. A diagonal element of the full
parabolic fixes the first coordinate and scales the other two. The elementary
SL₂ shears and the coordinate interchange give the remaining congruences.
These are the literal coordinates used in the central-extension argument for
Aschbacher–Smith I.1.3–4 and GLS3 §6.1.
-/

@[expose] public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneRadical Representation.OrthogonalFourMinus

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity

variable (F : Type*) [Field F] (σ : F ≃+* F)
local notation "K" => FixedBy.subfield F σ
local notation "H" => hermitianMatrices F σ

@[simp] theorem fixed_apply (a : K) : σ (a : F) = a := a.property

/-- First diagonal coordinate. -/
def first : K →+ H where
  toFun a := ⟨!![a,0;0,0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [adjoint]⟩
  map_zero' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' a b := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Second diagonal coordinate. -/
def second : K →+ H where
  toFun a := ⟨!![0,0;0,a], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [adjoint]⟩
  map_zero' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' a b := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp

variable (hσ : Function.Involutive σ)

/-- The off-diagonal coordinate is over the matrix field itself. -/
def off : F →+ H where
  toFun a := ⟨!![0,a;σ a,0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [adjoint, hσ a]⟩
  map_zero' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Congruence on Hermitian matrices, also for singular matrices. -/
def action (A : Mat F) : H →+ H where
  toFun X := ⟨A * X.val * adjoint σ A, by
    change adjoint σ (A * X.val * adjoint σ A) = A * X.val * adjoint σ A
    rw [adjoint_mul, adjoint_mul, adjoint_involutive σ hσ, X.property, mul_assoc]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' X Y := by apply Subtype.ext; simp [mul_add, add_mul]

@[simp] theorem action_one (X : H) : action F σ hσ 1 X = X := by
  apply Subtype.ext
  simp [action, adjoint_one]

theorem action_mul (A B : Mat F) (X : H) :
    action F σ hσ (A * B) X = action F σ hσ A (action F σ hσ B X) := by
  apply Subtype.ext
  simp [action, adjoint_mul, mul_assoc]

theorem action_surjective (A : SpecialLinearGroup (Fin 2) F) :
    Function.Surjective (action F σ hσ A.val) := by
  intro X
  refine ⟨action F σ hσ (A⁻¹).val X, ?_⟩
  have hm : A.val * (A⁻¹).val = (1 : Mat F) :=
    congrArg (fun C : SpecialLinearGroup (Fin 2) F => C.val) (mul_inv_cancel A)
  rw [← action_mul, hm, action_one]

/-- Exhaustiveness of the three additive coordinates. -/
theorem decomposition (X : H) :
    ∃ a b : K, ∃ z : F,
      X = first F σ a + second F σ b + off F σ hσ z := by
  have hx (i j : Fin 2) : σ (X.val j i) = X.val i j :=
    congrFun (congrFun X.property i) j
  refine ⟨⟨X.val 0 0, hx 0 0⟩, ⟨X.val 1 1, hx 1 1⟩, X.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [first, second, off, hx]

/-- The extra full-parabolic torus on the marked plane. -/
def torusMatrix (c : K) : Mat F := !![1,0;0,c]

@[simp] theorem torus_first (c a : K) :
    action F σ hσ (torusMatrix F σ c) (first F σ a) = first F σ a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, torusMatrix, first, adjoint, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp] theorem torus_second (c b : K) :
    action F σ hσ (torusMatrix F σ c) (second F σ b) = second F σ (c * c * b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, torusMatrix, second, adjoint, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      mul_comm, mul_left_comm]

@[simp] theorem torus_off (c : K) (z : F) :
    action F σ hσ (torusMatrix F σ c) (off F σ hσ z) = off F σ hσ (c * z) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, torusMatrix, off, adjoint, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      mul_comm]

variable [CharP F 2]

/-- An elementary upper shear in the literal SL₂ Levi. -/
def shear (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,t;0,1], by simp [Matrix.det_fin_two]⟩

/-- Interchange of the two coordinates; characteristic two makes it special linear. -/
def interchange : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [CharP F 2] in
@[simp] theorem shear_first (t : F) (a : K) :
    action F σ hσ (shear F t).val (first F σ a) = first F σ a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, shear, first, adjoint, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- Norms of matrix-field parameters lie in the fixed field. -/
def norm (t : F) : K := ⟨t * σ t, by simp [hσ t, mul_comm]⟩

omit [CharP F 2] in
theorem shear_second (t : F) (b : K) :
    action F σ hσ (shear F t).val (second F σ b) =
      first F σ (norm F σ hσ t * b) + second F σ b + off F σ hσ (t * b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, shear, first, second, off, norm, adjoint, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, mul_comm, mul_left_comm]

@[simp] theorem interchange_first (a : K) :
    action F σ hσ (interchange F).val (first F σ a) = second F σ a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action, interchange, first, second, adjoint, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- Full-parabolic invariance kills every additive pairing on the Hermitian
radical. Only a fixed scalar different from zero and one is required. -/
theorem invariant_pairing_zero {V : Type*} [AddCommGroup V]
    (B : H →+ H →+ V) (c : K) (hc1 : c ≠ 1)
    (hT : ∀ X Y, B (action F σ hσ (torusMatrix F σ c) X)
      (action F σ hσ (torusMatrix F σ c) Y) = B X Y)
    (hL : ∀ (A : SpecialLinearGroup (Fin 2) F) X Y,
      B (action F σ hσ A.val X) (action F σ hσ A.val Y) = B X Y)
    (X Y : H) : B X Y = 0 := by
  have hc2 : c * c - 1 ≠ 0 := by
    intro he
    have he' : c * c = 1 := sub_eq_zero.mp he
    rcases mul_self_eq_one_iff.mp he' with h | h
    · exact hc1 h
    · exact hc1 (by simpa only [CharTwo.neg_eq] using h)
  have hPQ (a b : K) : B (first F σ a) (second F σ b) = 0 := by
    let z := b / (c * c - 1)
    have hi := hT (first F σ a) (second F σ z)
    simp only [torus_first, torus_second] at hi
    have hz : b = c * c * z - z := by
      calc
        b = z * (c * c - 1) := (div_mul_cancel₀ b hc2).symm
        _ = _ := by ring
    rw [hz, map_sub, map_sub, hi, sub_self]
  have hcF : (c : F) - 1 ≠ 0 := by
    intro he
    exact hc1 (Subtype.ext (sub_eq_zero.mp he))
  have hPO (a : K) (b : F) : B (first F σ a) (off F σ hσ b) = 0 := by
    let z := b / ((c : F) - 1)
    have hi := hT (first F σ a) (off F σ hσ z)
    simp only [torus_first, torus_off] at hi
    have hz : b = (c : F) * z - z := by
      calc
        b = z * ((c : F) - 1) := (div_mul_cancel₀ b hcF).symm
        _ = _ := by ring
    rw [hz, map_sub, map_sub, hi, sub_self]
  have hPP (a b : K) : B (first F σ a) (first F σ b) = 0 := by
    have hi := hL (shear F 1) (first F σ a) (second F σ b)
    rw [shear_first, shear_second] at hi
    have hn : norm F σ hσ 1 = 1 := by apply Subtype.ext; simp [norm]
    simpa only [hn, one_mul, map_add, hPQ, hPO, add_zero] using hi
  have hP (a : K) (Z : H) : B (first F σ a) Z = 0 := by
    obtain ⟨b, d, z, rfl⟩ := decomposition F σ hσ Z
    simp only [map_add, hPP, hPQ, hPO, add_zero]
  have hQ (a : K) (Z : H) : B (second F σ a) Z = 0 := by
    obtain ⟨W, rfl⟩ := action_surjective F σ hσ (interchange F) Z
    simpa only [interchange_first, hP] using hL (interchange F) (first F σ a) W
  have hO (t : F) (Z : H) : B (off F σ hσ t) Z = 0 := by
    obtain ⟨W, rfl⟩ := action_surjective F σ hσ (shear F t) Z
    have hi := hL (shear F t) (second F σ 1) W
    rw [shear_second] at hi
    simpa only [Subfield.coe_one, mul_one, map_add, AddMonoidHom.add_apply,
      hP, hQ, zero_add] using hi
  obtain ⟨a, b, z, rfl⟩ := decomposition F σ hσ X
  simp only [map_add, AddMonoidHom.add_apply, hP, hQ, hO, zero_add]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity
