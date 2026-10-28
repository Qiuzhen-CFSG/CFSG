module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# Finite-field orthogonal root and torus coordinates

The root is the actual Siegel transformation with direction `eᵢ` and parameter
`a fⱼ`. Diagonal isometries have inverse entries on the paired coordinates.
The coordinate formulas prove injectivity, diagonal conjugation, the six-root
coroot identity, and an expression for every diagonal square as a commutator.
All statements hold over arbitrary fields; no algebraic closure is used.
These are the elementary orthogonal matrices of GLS3 §2.7
(`refs/KGroup/GLS3/chapter2.tex`). They supply the membership and normalization
steps for the Cartan obstruction in quasithin A.2.18, printed p.40.
-/

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
open scoped commutatorElement
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
variable {F : Type u} [Field F] {r : ℕ}
abbrev O (r : ℕ) (F : Type u) [Field F] := ↥(quadraticIsometrySubgroup (k := F) (V := VectorD r F) (formD r F))

def root {i j : Fin r} (hij : i ≠ j) (a : F) : O r F :=
  siegelElement (formD r F) (e i) (a • f j) (formD_e i) (by
    rw [map_smul, polarD_f]
    simp [e, Pi.single_apply, hij])

@[simp] theorem root_apply_left {i j : Fin r} (hij : i ≠ j) (a : F)
    (x : VectorD r F) (k : Fin r) :
    (root hij a).val x (.inl k) = x (.inl k) + if k = i then a * x (.inl j) else 0 := by
  change (Quadratic.siegel (formD r F) (e i) (a • f j) x) (.inl k) = _
  simp only [Quadratic.siegel, map_smul, polarD_e, polarD_f,
    QuadraticMap.map_smul, formD_f, smul_zero, zero_mul, zero_smul, sub_zero]
  by_cases h : k = i <;> simp [e, f, h, Pi.single_apply, mul_comm]

@[simp] theorem root_apply_right {i j : Fin r} (hij : i ≠ j) (a : F)
    (x : VectorD r F) (k : Fin r) :
    (root hij a).val x (.inr k) = x (.inr k) - if k = j then a * x (.inr i) else 0 := by
  change (Quadratic.siegel (formD r F) (e i) (a • f j) x) (.inr k) = _
  simp only [Quadratic.siegel, map_smul, polarD_e, polarD_f,
    QuadraticMap.map_smul, formD_f, smul_zero, zero_mul, zero_smul, sub_zero]
  by_cases h : k = j <;> simp [e, f, h, Pi.single_apply, mul_comm]

theorem root_mem_elementary {i j : Fin r} (hij : i ≠ j) (a : F) :
    root hij a ∈ elementarySubgroup (formD r F) := siegelElement_mem _ _ _ _ _

def rootHom {i j : Fin r} (hij : i ≠ j) : Multiplicative F →* O r F where
  toFun a := root hij a.toAdd
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext k
    cases k <;> simp
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext k
    cases k with
    | inl k =>
      change (root hij (a.toAdd + b.toAdd)).val x (.inl k) =
        (root hij a.toAdd).val ((root hij b.toAdd).val x) (.inl k)
      simp only [root_apply_left, if_neg hij.symm, add_zero]
      split_ifs <;> ring
    | inr k =>
      change (root hij (a.toAdd + b.toAdd)).val x (.inr k) =
        (root hij a.toAdd).val ((root hij b.toAdd).val x) (.inr k)
      simp only [root_apply_right, if_neg hij, sub_zero]
      split_ifs <;> ring

theorem rootHom_injective {i j : Fin r} (hij : i ≠ j) :
    Function.Injective (rootHom (F := F) hij) := by
  intro a b hab
  have h := congrArg (fun g : O r F => g.val (e j) (.inl i)) hab
  simpa [rootHom, e, Pi.single_apply, hij] using h

def diagonalLinear (d : Fin r → Fˣ) : VectorD r F ≃ₗ[F] VectorD r F where
  toFun x := Sum.elim (fun i => (d i : F) * x (.inl i))
    (fun i => ((d i)⁻¹ : Fˣ) * x (.inr i))
  invFun x := Sum.elim (fun i => ((d i)⁻¹ : Fˣ) * x (.inl i))
    (fun i => (d i : F) * x (.inr i))
  left_inv x := by funext i; cases i <;> simp [mul_assoc]
  right_inv x := by funext i; cases i <;> simp [mul_assoc]
  map_add' x y := by funext i; cases i <;> simp [mul_add]
  map_smul' a x := by funext i; cases i <;> simp [mul_left_comm]

def diagonal (d : Fin r → Fˣ) : O r F :=
  ⟨diagonalLinear d, (mem_quadraticIsometrySubgroup _ _).mpr (by
    intro x
    simp only [formD_apply, diagonalLinear, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_assoc, mul_left_comm, mul_comm])⟩

@[simp] theorem diagonal_left (d : Fin r → Fˣ) (x : VectorD r F) (i : Fin r) :
    (diagonal d).val x (.inl i) = (d i : F) * x (.inl i) := rfl
@[simp] theorem diagonal_right (d : Fin r → Fˣ) (x : VectorD r F) (i : Fin r) :
    (diagonal d).val x (.inr i) = ((d i)⁻¹ : Fˣ) * x (.inr i) := rfl

def diagonalHom : (Fin r → Fˣ) →* O r F where
  toFun := diagonal
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    cases i <;> simp
  map_mul' d c := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    cases i with
    | inl i => change (d i * c i : Fˣ) * x (.inl i) = (d i : F) * ((c i : F) * x (.inl i)); simp [mul_assoc]
    | inr i => change ((d i * c i)⁻¹ : Fˣ) * x (.inr i) = ((d i)⁻¹ : Fˣ) * (((c i)⁻¹ : Fˣ) * x (.inr i)); simp [mul_assoc, mul_comm]

theorem diagonalHom_injective : Function.Injective (diagonalHom (F := F) (r := r)) := by
  intro a b hab
  funext i
  apply Units.ext
  have h := congrArg (fun g : O r F => g.val (e i) (.inl i)) hab
  simpa [diagonalHom, e] using h

theorem diagonal_conj_root (d : Fin r → Fˣ) {i j : Fin r} (hij : i ≠ j) (a : F) :
    diagonal d * root hij a * (diagonal d)⁻¹ =
      root hij ((d i : F) * a * ((d j)⁻¹ : Fˣ)) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (diagonal d).val ((root hij a).val x) (.inl k) =
      (root hij ((d i : F) * a * ((d j)⁻¹ : Fˣ))).val ((diagonal d).val x) (.inl k)
    by_cases h : k = i <;> simp [h, mul_add, mul_assoc, mul_left_comm, mul_comm]
  | inr k =>
    change (diagonal d).val ((root hij a).val x) (.inr k) =
      (root hij ((d i : F) * a * ((d j)⁻¹ : Fˣ))).val ((diagonal d).val x) (.inr k)
    by_cases h : k = j <;> simp [h, mul_sub, mul_assoc, mul_left_comm, mul_comm]

def pairEntries (i j : Fin r) (t : Fˣ) : Fin r → Fˣ :=
  fun k => if k = i then t else if k = j then t⁻¹ else 1

/-- The usual six-root expression for a coroot, checked on the actual coordinates. -/
theorem pair_diagonal_word {i j : Fin r} (hij : i ≠ j) (t : Fˣ) :
    diagonal (pairEntries i j t) =
      root hij (t : F) * root hij.symm (-((t⁻¹ : Fˣ) : F)) * root hij (t : F) *
      root hij (-1) * root hij.symm 1 * root hij (-1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (diagonal (pairEntries i j t)).val x (.inl k) =
      (root hij (t : F)).val ((root hij.symm (-((t⁻¹ : Fˣ) : F))).val
        ((root hij (t : F)).val ((root hij (-1 : F)).val
          ((root hij.symm (1 : F)).val ((root hij (-1 : F)).val x))))) (.inl k)
    simp only [diagonal_left, root_apply_left]
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pairEntries, hi, hj, hij, hij.symm, Units.val_inv_eq_inv_val] <;>
      field_simp <;> ring
  | inr k =>
    change (diagonal (pairEntries i j t)).val x (.inr k) =
      (root hij (t : F)).val ((root hij.symm (-((t⁻¹ : Fˣ) : F))).val
        ((root hij (t : F)).val ((root hij (-1 : F)).val
          ((root hij.symm (1 : F)).val ((root hij (-1 : F)).val x))))) (.inr k)
    simp only [diagonal_right, root_apply_right]
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pairEntries, hi, hj, hij, hij.symm, Units.val_inv_eq_inv_val] <;>
      field_simp <;> ring

theorem pair_diagonal_mem {i j : Fin r} (hij : i ≠ j) (t : Fˣ) :
    diagonal (pairEntries i j t) ∈ elementarySubgroup (formD r F) := by
  rw [pair_diagonal_word hij]
  repeat apply Subgroup.mul_mem
  all_goals exact root_mem_elementary _ _

/-- Exchange the two halves of every hyperbolic pair. -/
def flipLinear : VectorD r F ≃ₗ[F] VectorD r F where
  toFun x := Sum.elim (fun i => x (.inr i)) (fun i => x (.inl i))
  invFun x := Sum.elim (fun i => x (.inr i)) (fun i => x (.inl i))
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' a x := by funext i; cases i <;> rfl

def flip : O r F := ⟨flipLinear, (mem_quadraticIsometrySubgroup _ _).mpr (by
  intro x
  simp only [formD_apply, flipLinear, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _))⟩

@[simp] theorem flip_inv : (flip (r := r) (F := F))⁻¹ = flip := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

@[simp] theorem flip_left (x : VectorD r F) (i : Fin r) :
    (flip (r := r) (F := F)).val x (.inl i) = x (.inr i) := rfl
@[simp] theorem flip_right (x : VectorD r F) (i : Fin r) :
    (flip (r := r) (F := F)).val x (.inr i) = x (.inl i) := rfl

theorem diagonal_square_commutator (d : Fin r → Fˣ) :
    ⁅diagonal d, flip⁆ = diagonal (d ^ 2) := by
  have hinv : (diagonal d)⁻¹ = diagonal d⁻¹ := (map_inv diagonalHom d).symm
  rw [commutatorElement_def, hinv, flip_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl i =>
    change (diagonal d).val ((flip (r := r) (F := F)).val ((diagonal d⁻¹).val ((flip (r := r) (F := F)).val x))) (.inl i) = _
    simp [pow_two, mul_assoc]
  | inr i =>
    change (diagonal d).val ((flip (r := r) (F := F)).val ((diagonal d⁻¹).val ((flip (r := r) (F := F)).val x))) (.inr i) = _
    simp [pow_two, mul_assoc]

theorem diagonal_square_mem_commutator (d : Fin r → Fˣ) :
    diagonal (d ^ 2) ∈ commutator (O r F) := by
  rw [← diagonal_square_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
