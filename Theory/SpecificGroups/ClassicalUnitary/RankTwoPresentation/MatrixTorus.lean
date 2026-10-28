module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixWeyl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Full torus action and rank-one Bruhat equations

These are literal matrix identities for arbitrary characteristic-two fields
with involution. In dimension five the Hermitian constraint is retained.
Source: Steinberg, Lectures on Chevalley Groups, Lemmas 24 and 63–64.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Matrix
variable {E : Type*} [Field E] (σ : E ≃+* E)

namespace Matrix4

theorem H_A (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * A σ v = A σ ((a/b)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [A,map_mul,map_div₀] <;>
    field_simp

theorem H_C (hσ : Function.Involutive σ) (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * C σ v = C σ ((a*σ b)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [C,map_mul,hσ b] <;>
    field_simp

theorem H_B (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * B v = B ((b*σ b)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [B]
  field_simp

theorem H_D (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * D v = D ((a*σ a)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [D]
  field_simp

end Matrix4

namespace Matrix5

theorem H_A (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * A σ v = A σ ((a/b)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [A,delta,map_mul,map_div₀] <;>
    field_simp

theorem H_C (hσ : Function.Involutive σ) (a b : E) (ha : a≠0) (hb : b≠0) (v : E) :
    H σ a b * C σ v = C σ ((a*σ b)*v) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [C,delta,map_mul,hσ b] <;>
    field_simp

theorem H_B (hσ : Function.Involutive σ) (a b : E) (ha : a≠0) (hb : b≠0) (x z : E) :
    H σ a b * B σ x z = B σ ((b/delta σ a b)*x) ((b*σ b)*z) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [B,delta,map_mul,map_div₀,hσ a,hσ b] <;>
    field_simp

theorem H_D (hσ : Function.Involutive σ) (a b : E) (ha : a≠0) (hb : b≠0) (x z : E) :
    H σ a b * D σ x z = D σ ((a/delta σ a b)*x) ((a*σ a)*z) * H σ a b := by
  have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
  have hsb : σ b≠0 := (map_ne_zero σ).mpr hb
  ext i j
  simp only [H,Matrix.diagonal_mul,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [D,delta,map_mul,map_div₀,hσ a,hσ b] <;>
    field_simp

end Matrix5
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
