module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
import Mathlib.Tactic.Abel

/-!
# Complete quadratic expansion and linear separation

For any family of half-matrices, the quadratic pullback of a member of its
linear span belongs to the span of all diagonal and polarized basis terms.
Consequently preservation of a form space by `1 + D` puts the linear pullback
term in the sum of that space and this quadratic span. A separating linear
calculation can leave a single binary line, which is rejected when its
quadratic term vanishes and its linear term leaves the original form space.

This is the algebraic reduction in the finite route documented in
`MathieuSeedCentralizer/KernelBound/source/README.md`. The concrete separation
and source-space calibration are separate certificate obligations.
-/

@[expose] public section

open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
open Coordinates

/-- The linear part of pullback by `1 + D`. -/
def linearTerm (R : HalfMatrix) : HalfMatrix →ₗ[ZMod 2] HalfMatrix where
  toFun D := Dᵀ * R + R * D
  map_add' D E := by simp only [transpose_add, add_mul, mul_add]; abel
  map_smul' a D := by
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, RingHom.id_apply]

/-- The quadratic part of pullback by `1 + D`. -/
def quadraticTerm (R D : HalfMatrix) : HalfMatrix := Dᵀ * R * D

/-- The complete polarized quadratic term. -/
def polarTerm (R D E : HalfMatrix) : HalfMatrix := Dᵀ * R * E + Eᵀ * R * D

/-- All diagonal and polarized terms; no coefficient in the expansion is omitted. -/
def quadraticSpan {ι : Type*} (R : HalfMatrix) (b : ι → HalfMatrix) :
    Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) (Set.range (fun i => quadraticTerm R (b i)) ∪
    Set.range (fun p : ι × ι => polarTerm R (b p.1) (b p.2)))

theorem polarTerm_mem_quadraticSpan {ι : Type*} (R : HalfMatrix) (b : ι → HalfMatrix)
    {D E : HalfMatrix} (hD : D ∈ Submodule.span (ZMod 2) (Set.range b))
    (hE : E ∈ Submodule.span (ZMod 2) (Set.range b)) :
    polarTerm R D E ∈ quadraticSpan R b := by
  induction hD, hE using Submodule.span_induction₂ with
  | mem_mem D E hD hE =>
    rcases hD with ⟨i, rfl⟩
    rcases hE with ⟨j, rfl⟩
    exact Submodule.subset_span (Or.inr ⟨(i, j), rfl⟩)
  | zero_left E hE => simp only [polarTerm, transpose_zero, zero_mul, mul_zero, add_zero]; exact Submodule.zero_mem _
  | zero_right D hD => simp only [polarTerm, transpose_zero, zero_mul, mul_zero, add_zero]; exact Submodule.zero_mem _
  | add_left D E F hD hE hF ihD ihE =>
    have h := (quadraticSpan R b).add_mem ihD ihE
    convert h using 1
    simp only [polarTerm, transpose_add, add_mul, mul_add]
    abel
  | add_right D E F hD hE hF ihE ihF =>
    have h := (quadraticSpan R b).add_mem ihE ihF
    convert h using 1
    simp only [polarTerm, transpose_add, add_mul, mul_add]
    abel
  | smul_left a D E hD hE ih =>
    simpa only [polarTerm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      using (quadraticSpan R b).smul_mem a ih
  | smul_right a D E hD hE ih =>
    simpa only [polarTerm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      using (quadraticSpan R b).smul_mem a ih

theorem quadraticTerm_add (R D E : HalfMatrix) :
    quadraticTerm R (D + E) = quadraticTerm R D + quadraticTerm R E + polarTerm R D E := by
  simp only [quadraticTerm, polarTerm, transpose_add, add_mul, mul_add]
  abel

theorem quadraticTerm_mem_quadraticSpan {ι : Type*} (R : HalfMatrix) (b : ι → HalfMatrix)
    {D : HalfMatrix} (hD : D ∈ Submodule.span (ZMod 2) (Set.range b)) :
    quadraticTerm R D ∈ quadraticSpan R b := by
  induction hD using Submodule.span_induction with
  | mem D hD =>
    rcases hD with ⟨i, rfl⟩
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  | zero => simp only [quadraticTerm, transpose_zero, zero_mul]; exact Submodule.zero_mem _
  | add D E hD hE ihD ihE =>
    rw [quadraticTerm_add]
    exact (quadraticSpan R b).add_mem ((quadraticSpan R b).add_mem ihD ihE)
      (polarTerm_mem_quadraticSpan R b hD hE)
  | smul a D hD ih =>
    simpa only [quadraticTerm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      using (quadraticSpan R b).smul_mem (a * a) ih

theorem pullback_one_add (R D : HalfMatrix) :
    (1 + D)ᵀ * R * (1 + D) = R + (linearTerm R D + quadraticTerm R D) := by
  simp only [linearTerm, LinearMap.coe_mk, AddHom.coe_mk, quadraticTerm,
    transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one]
  abel

theorem linearTerm_mem_sup_of_pullback {ι : Type*} (R : HalfMatrix) (b : ι → HalfMatrix)
    (S : Submodule (ZMod 2) HalfMatrix) (hR : R ∈ S) {D : HalfMatrix}
    (hD : D ∈ Submodule.span (ZMod 2) (Set.range b))
    (hP : (1 + D)ᵀ * R * (1 + D) ∈ S) :
    linearTerm R D ∈ S ⊔ quadraticSpan R b := by
  have hdiff : linearTerm R D + quadraticTerm R D ∈ S := by
    simpa only [pullback_one_add, add_sub_cancel_left] using S.sub_mem hP hR
  have hlin := (S ⊔ quadraticSpan R b).sub_mem (Submodule.mem_sup_left hdiff)
    (Submodule.mem_sup_right (quadraticTerm_mem_quadraticSpan R b hD))
  simpa only [add_sub_cancel_right] using hlin

/-- Separation leaves at most a line. Its zero quadratic term and nonzero linear
residue reject the nonzero point of that line over the binary field. -/
theorem eq_zero_of_separation {ι : Type*} (R : HalfMatrix) (b : ι → HalfMatrix)
    (S : Submodule (ZMod 2) HalfMatrix) (top : HalfMatrix)
    (hR : R ∈ S)
    (hsep : ∀ D ∈ Submodule.span (ZMod 2) (Set.range b),
      linearTerm R D ∈ S ⊔ quadraticSpan R b → ∃ a : ZMod 2, D = a • top)
    (htopQ : quadraticTerm R top = 0) (htopL : linearTerm R top ∉ S)
    {D : HalfMatrix} (hD : D ∈ Submodule.span (ZMod 2) (Set.range b))
    (hP : (1 + D)ᵀ * R * (1 + D) ∈ S) : D = 0 := by
  obtain ⟨a, rfl⟩ := hsep D hD (linearTerm_mem_sup_of_pullback R b S hR hD hP)
  have ha : a = 0 ∨ a = 1 := (by decide +kernel : ∀ x : ZMod 2, x = 0 ∨ x = 1) a
  rcases ha with rfl | rfl
  · exact zero_smul _ _
  · simp only [one_smul] at hP ⊢
    have hdiff := S.sub_mem hP hR
    rw [pullback_one_add, htopQ, add_zero, add_sub_cancel_left] at hdiff
    exact False.elim (htopL hdiff)

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
