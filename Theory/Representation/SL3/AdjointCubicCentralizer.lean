module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Tactic.FinCases

/-!
# The cubic fixed space in the three-dimensional adjoint representation

For a nonidentity scalar ω, conjugation by diag(ω,1,1) fixes precisely the
block diagonal matrices. Inside the trace kernel, every such matrix is
uniquely diag(-tr(D),D), for a two-by-two matrix D. This identifies the
four-dimensional fixed space with End(K²), equivariantly for the lower SL₂.
The action and the intertwiner are actual matrix operations; no recognition
or irreducibility theorem is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma
B.4.14, printed p.98. This is the concrete fixed-space computation for the
untwisted adjoint action, not the source recognition assertion.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open Matrix
namespace Representation.SL3.AdjointCubicCentralizer
noncomputable section
variable (K : Type*) [Field K]
abbrev Mat2 := Matrix (Fin 2) (Fin 2) K
abbrev Mat3 := Matrix (Fin 3) (Fin 3) K

def block (a : K) (D : Mat2 K) : Mat3 K :=
  !![a, 0, 0; 0, D 0 0, D 0 1; 0, D 1 0, D 1 1]

def lowerBlock : Mat3 K →ₗ[K] Mat2 K where
  toFun X i j := X i.succ j.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem lowerBlock_block (a : K) (D : Mat2 K) :
    lowerBlock K (block K a D) = D := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem block_mul (a b : K) (D E : Mat2 K) :
    block K a D * block K b E = block K (a*b) (D*E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

@[simp] theorem block_one : block K 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

@[simp] theorem trace_block (a : K) (D : Mat2 K) :
    Matrix.trace (block K a D) = a + Matrix.trace D := by
  simp [Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two, block, add_assoc]

def traceBlock : Mat2 K →ₗ[K] Mat3 K where
  toFun D := block K (-Matrix.trace D) D
  map_add' D E := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [block, Matrix.trace_add, add_comm]
  map_smul' c D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [block, Matrix.trace_smul]

@[simp] theorem trace_traceBlock (D : Mat2 K) :
    Matrix.trace (traceBlock K D) = 0 := by
  exact (trace_block K _ D).trans (neg_add_cancel _)

@[simp] theorem lowerBlock_traceBlock (D : Mat2 K) :
    lowerBlock K (traceBlock K D) = D := lowerBlock_block K _ D

def diagonalUnit (ω : Kˣ) : (Mat3 K)ˣ where
  val := block K (ω : K) 1
  inv := block K (↑ω⁻¹ : K) 1
  val_inv := by rw [block_mul]; simp
  inv_val := by rw [block_mul]; simp

def fixedSpace (ω : Kˣ) : Submodule K (Mat3 K) where
  carrier := {X | Matrix.trace X = 0 ∧ (diagonalUnit K ω).val * X = X * (diagonalUnit K ω).val}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX,hX'⟩ ⟨hY,hY'⟩
    exact ⟨by simp [hX,hY], by simp [mul_add, add_mul, hX',hY']⟩
  smul_mem' := by
    rintro c X ⟨hX,hX'⟩
    exact ⟨by simp [hX], by simpa using congrArg (c • ·) hX'⟩

@[simp] theorem mem_fixedSpace (ω : Kˣ) (X : Mat3 K) :
    X ∈ fixedSpace K ω ↔ Matrix.trace X = 0 ∧
      (diagonalUnit K ω).val * X = X * (diagonalUnit K ω).val := Iff.rfl

theorem mem_fixedSpace_iff_fixed (ω : Kˣ) (X : Mat3 K) :
    X ∈ fixedSpace K ω ↔ Matrix.trace X = 0 ∧
      (diagonalUnit K ω).val * X * (diagonalUnit K ω)⁻¹.val = X := by
  rw [mem_fixedSpace]
  apply and_congr_right
  intro _
  constructor
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  · intro h
    have hh := congrArg (fun Y => Y * (diagonalUnit K ω).val) h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hh

theorem traceBlock_mem (ω : Kˣ) (D : Mat2 K) :
    traceBlock K D ∈ fixedSpace K ω := by
  refine ⟨trace_traceBlock K D, ?_⟩
  change block K (ω : K) 1 * block K (-Matrix.trace D) D =
    block K (-Matrix.trace D) D * block K (ω : K) 1
  rw [block_mul, block_mul]
  simp [mul_comm]

private theorem offDiagonal_zero (ω : Kˣ) (hω : (ω : K) ≠ 1)
    (X : fixedSpace K ω) :
    X.val 0 1 = 0 ∧ X.val 0 2 = 0 ∧ X.val 1 0 = 0 ∧ X.val 2 0 = 0 := by
  have he := X.property.2
  have h (i j : Fin 3) := congrArg (fun M : Mat3 K => M i j) he
  have h01 := h 0 1
  have h02 := h 0 2
  have h10 := h 1 0
  have h20 := h 2 0
  simp [diagonalUnit, block, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02 h10 h20
  have kill (z : K) (hz : (ω : K) * z = z) : z = 0 := by
    have hz' : ((ω : K) - 1) * z = 0 := by rw [sub_mul, one_mul, hz, sub_self]
    exact (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr hω)
  exact ⟨kill _ h01, kill _ h02, kill _ (by simpa [mul_comm] using h10.symm),
    kill _ (by simpa [mul_comm] using h20.symm)⟩

theorem traceBlock_lowerBlock (ω : Kˣ) (hω : (ω : K) ≠ 1)
    (X : fixedSpace K ω) : traceBlock K (lowerBlock K X.val) = X.val := by
  obtain ⟨h01,h02,h10,h20⟩ := offDiagonal_zero K ω hω X
  have ht := X.property.1
  simp only [Matrix.trace, Fin.sum_univ_three] at ht
  have h00 : -(X.val 1 1 + X.val 2 2) = X.val 0 0 := by
    symm
    apply (eq_neg_iff_add_eq_zero).mpr
    simpa only [Matrix.diag, add_assoc] using ht
  change block K (-(Matrix.trace (lowerBlock K X.val))) (lowerBlock K X.val) = X.val
  have hentry (i j : Fin 2) : lowerBlock K X.val i j = X.val i.succ j.succ := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, hentry, Matrix.trace, Fin.sum_univ_two] <;> simp_all

def fixedEquiv (ω : Kˣ) (hω : (ω : K) ≠ 1) : fixedSpace K ω ≃ₗ[K] Mat2 K where
  toFun X := lowerBlock K X.val
  invFun D := ⟨traceBlock K D, traceBlock_mem K ω D⟩
  left_inv X := Subtype.ext (traceBlock_lowerBlock K ω hω X)
  right_inv := lowerBlock_traceBlock K
  map_add' X Y := map_add (lowerBlock K) X.val Y.val
  map_smul' c X := map_smul (lowerBlock K) c X.val

theorem finrank_fixedSpace (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    Module.finrank K (fixedSpace K ω) = 4 := by
  rw [(fixedEquiv K ω hω).finrank_eq]
  change Module.finrank K (Matrix (Fin 2) (Fin 2) K) = 4
  rw [Module.finrank_matrix]
  simp


/-- Conjugation on square matrices by the actual matrix units. -/
def conjugation (n : ℕ) :
    Representation K (Matrix (Fin n) (Fin n) K)ˣ (Matrix (Fin n) (Fin n) K) where
  toFun g :=
    { toFun X := g.val * X * g⁻¹.val
      map_add' X Y := by simp [mul_add, add_mul]
      map_smul' c X := by simp }
  map_one' := by ext X i j; simp
  map_mul' g h := by
    ext X i j
    change ((g*h).val * X * (g*h)⁻¹.val) i j = _
    simp [mul_assoc]

/-- The standard lower two-dimensional Levi subgroup. -/
def levi : Matrix.SpecialLinearGroup (Fin 2) K →* (Mat3 K)ˣ where
  toFun g :=
    { val := block K 1 g.val
      inv := block K 1 g⁻¹.val
      val_inv := by
        rw [block_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        simp
      inv_val := by
        rw [block_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        simp }
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    change block K 1 (g*h).val = block K 1 g.val * block K 1 h.val
    rw [block_mul, Matrix.SpecialLinearGroup.coe_mul, one_mul]

/-- Conjugation on the two-space, restricted to its determinant-one group. -/
def twoAction : Representation K (Matrix.SpecialLinearGroup (Fin 2) K) (Mat2 K) :=
  (conjugation K 2).comp Matrix.SpecialLinearGroup.toGL

/-- The lower Levi acts on the trace block by its genuine conjugation action. -/
theorem traceBlock_conjugate (g : Matrix.SpecialLinearGroup (Fin 2) K) (D : Mat2 K) :
    (levi K g).val * traceBlock K D * (levi K g)⁻¹.val =
      traceBlock K (twoAction K g D) := by
  change block K 1 g.val * block K (-Matrix.trace D) D * block K 1 g⁻¹.val =
    block K (-Matrix.trace (g.val * D * g⁻¹.val)) (g.val * D * g⁻¹.val)
  rw [block_mul, block_mul, one_mul, mul_one]
  congr 1
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

/-- The fixed space of the cubic element is stable under the commuting Levi. -/
def fixedSubrepresentation (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    Subrepresentation ((conjugation K 3).comp (levi K)) where
  toSubmodule := fixedSpace K ω
  apply_mem_toSubmodule g X hX := by
    have he : traceBlock K (lowerBlock K X) = X :=
      traceBlock_lowerBlock K ω hω ⟨X,hX⟩
    change (levi K g).val * X * (levi K g)⁻¹.val ∈ fixedSpace K ω
    rw [← he, traceBlock_conjugate]
    exact traceBlock_mem K ω _

abbrev fixedAction (ω : Kˣ) (hω : (ω : K) ≠ 1) :=
  (fixedSubrepresentation K ω hω).toRepresentation

/-- The actual fixed-space action is the endomorphism representation of SL₂. -/
def fixedRepresentationEquiv (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    (fixedAction K ω hω).Equiv (twoAction K) :=
  .mk (fixedEquiv K ω hω) (by
    intro g
    apply LinearMap.ext
    intro X
    change lowerBlock K ((levi K g).val * X.val * (levi K g)⁻¹.val) =
      twoAction K g (lowerBlock K X.val)
    rw [← traceBlock_lowerBlock K ω hω X, traceBlock_conjugate,
      lowerBlock_traceBlock, lowerBlock_traceBlock])

end
end Representation.SL3.AdjointCubicCentralizer
