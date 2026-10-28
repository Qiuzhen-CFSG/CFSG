module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Trace-zero matrices for binary SL₅

This is conjugation on the literal kernel of the 5×5 matrix trace. Its
highest-root matrix E₀₄ satisfies the two endpoint rank-one relations. A
matrix commuting with all positive-root transvections is a scalar matrix
plus a multiple of E₀₄. Since the dimension is odd, the trace-zero condition
kills the scalar part. Thus the positive-root fixed space is exactly the
highest-root line. The trace map is onto, so the module has dimension 24.

These concrete calculations support the adjoint realization and its
common-centralizer estimates, independently of any highest-weight catalogue.
Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Lemma 4.5 step 2, pp.23–24.
-/

@[expose] public noncomputable section
namespace Representation.SL5Adjoint
open Matrix
open SL5TenDimensional.Classification
abbrev Group := SL5TenDimensional.Group
abbrev Mat := Matrix (Fin 5) (Fin 5) (ZMod 2)

/-- Ordinary matrix conjugation by the marked special linear group. -/
def conjugation : Representation (ZMod 2) Group Mat where
  toFun g :=
    { toFun X := g.val * X * g⁻¹.val
      map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' c X := by simp }
  map_one' := by ext X i j; simp
  map_mul' g h := by
    ext X i j
    change ((g * h).val * X * (g * h)⁻¹.val) i j =
      (g.val * (h.val * X * h⁻¹.val) * g⁻¹.val) i j
    simp [Matrix.SpecialLinearGroup.coe_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

/-- The invariant kernel of the ordinary matrix trace. -/
def traceZero : Subrepresentation conjugation where
  toSubmodule := (Matrix.traceLinearMap (Fin 5) (ZMod 2) (ZMod 2)).ker
  apply_mem_toSubmodule g X hX := by
    change Matrix.trace (g.val * X * g⁻¹.val) = 0
    rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    exact hX

abbrev Space := (Matrix.traceLinearMap (Fin 5) (ZMod 2) (ZMod 2)).ker
abbrev action : Representation (ZMod 2) Group Space := traceZero.toRepresentation

@[simp] theorem action_val (g : Group) (X : Space) :
    (action g X).val = g.val * X.val * g⁻¹.val := rfl

/-- An off-diagonal matrix unit in the trace kernel. -/
def root (i j : Fin 5) (hij : i ≠ j) : Space :=
  ⟨Matrix.single i j 1, by simp [LinearMap.mem_ker, Matrix.trace_single_eq_of_ne, hij]⟩

/-- The matrix E₀₄, with the source positive-root convention. -/
def highestRoot : Space := root 0 4 (by decide)

theorem highestRoot_ne_zero : highestRoot ≠ 0 := by
  intro hz
  have := congrArg (fun X : Space => X.val 0 4) hz
  norm_num [highestRoot, root] at this

/-- E₀₄ has exactly the two endpoint highest-vector relations. -/
theorem highestRoot_local :
    LocalHighestVector action {0, 3} highestRoot := by
  constructor
  · intro i j hij
    apply Subtype.ext
    rw [action_val, Matrix.SpecialLinearGroup.transvection_inv]
    revert i j hij
    decide +kernel
  · intro i hi
    apply Subtype.ext
    rw [action_val, inv_eq_of_mul_eq_one_right (HeckeAction.swap_sq i)]
    revert i hi
    decide +kernel
  · intro i hi
    apply Subtype.ext
    change highestRoot.val + (action (simpleSwap i) highestRoot).val +
      (action (simpleLower i) highestRoot).val = 0
    rw [action_val, action_val, inv_eq_of_mul_eq_one_right (HeckeAction.swap_sq i)]
    simp only [simpleLower, Matrix.SpecialLinearGroup.transvection_inv]
    revert i hi
    decide +kernel

/-- The literal trace-zero matrix space has dimension twenty-four. -/
theorem finrank_space : Module.finrank (ZMod 2) Space = 24 := by
  have hs : Function.Surjective (Matrix.traceLinearMap (Fin 5) (ZMod 2) (ZMod 2)) := by
    intro c
    exact ⟨Matrix.single 0 0 c, by simp⟩
  have hh := (Matrix.traceLinearMap (Fin 5) (ZMod 2) (ZMod 2)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at hh
  have hm : Module.finrank (ZMod 2) Mat = 25 := by simp [Mat, Module.finrank_matrix]
  change 1 + Module.finrank (ZMod 2) Space = Module.finrank (ZMod 2) Mat at hh
  omega

/-- Fixed matrices are precisely the matrices commuting with the actor. -/
theorem fixed_iff_commute (g : Group) (X : Space) :
    action g X = X ↔ g.val * X.val = X.val * g.val := by
  rw [Subtype.ext_iff, action_val]
  constructor
  · intro h
    have hh := congrArg (fun A : Mat => A * g.val) h
    simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using hh
  · intro h
    rw [h, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

private theorem upper_commute {X : Space} (h : UpperFixed action X)
    (i j : Fin 5) (hij : i < j) :
    Matrix.single i j (1 : ZMod 2) * X.val = X.val * Matrix.single i j 1 := by
  have hh := (fixed_iff_commute _ X).mp (h i j hij)
  simpa only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    add_right_inj] using hh

/-- The positive-root fixed space is the highest-root line. -/
theorem upperFixed_eq_smul {X : Space} (h : UpperFixed action X) :
    X = X.val 0 4 • highestRoot := by
  have hd (i : Fin 5) : X.val i i = X.val 0 0 := by
    by_cases hi : i = 0
    · simp [hi]
    have he := congrArg (fun A : Mat => A 0 i)
      (upper_commute h 0 i (by omega))
    simpa using he
  have hd0 : X.val 0 0 = 0 := by
    have ht : Matrix.trace X.val = 0 := X.property
    simp only [Matrix.trace, Matrix.diag_apply, hd, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at ht
    rwa [show ((5 : ℕ) : ZMod 2) = 1 by decide, one_mul] at ht
  have hz (i j : Fin 5) (hij : i ≠ j) (hex : i ≠ 0 ∨ j ≠ 4) : X.val i j = 0 := by
    rcases hex with hi | hj
    · have he := congrArg (fun A : Mat => A 0 j)
        (upper_commute h 0 i (by omega))
      simpa [Matrix.mul_single_apply_of_ne (1 : ZMod 2) (0 : Fin 5) i (0 : Fin 5) j hij.symm X.val] using he
    · by_cases hi : i = 0
      · subst i
        have he := congrArg (fun A : Mat => A 0 4)
          (upper_commute h j 4 (by omega))
        simpa [Matrix.single_mul_apply_of_ne (1 : ZMod 2) j (4 : Fin 5) (0 : Fin 5) (4 : Fin 5) hij X.val] using he.symm
      · have he := congrArg (fun A : Mat => A 0 j)
          (upper_commute h 0 i (by omega))
        simpa [Matrix.mul_single_apply_of_ne (1 : ZMod 2) (0 : Fin 5) i (0 : Fin 5) j hij.symm X.val] using he
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;> simp [highestRoot, root, Matrix.single, hd, hd0]
  · by_cases hi : i = 0
    · subst i
      by_cases hj : j = 4
      · subst j; simp [highestRoot, root]
      · simp [highestRoot, root, Matrix.single, Ne.symm hj, hz 0 j hij (Or.inr hj)]
    · simp [highestRoot, root, Matrix.single, Ne.symm hi, hz i j hij (Or.inl hi)]

end Representation.SL5Adjoint
