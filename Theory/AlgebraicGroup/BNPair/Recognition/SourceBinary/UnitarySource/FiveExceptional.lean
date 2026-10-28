module
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# The exceptional U₅ coefficient system over the field of sixteen elements

Fong--Seitz II (8.35), printed pp.209--210, uses a primitive cube root ω
and θ²=θ+ω. We prove uniqueness by five explicit linear combinations and
verify the solution θ+1 using these two quadratic field relations. This
requires neither an opaque finite computation nor a determinant assumption.

The displayed equations are verified against the recovered PDF; in
particular the fourth right-hand side is θ⁴ and the fifth is ω²θ⁴.
Deriving this system from the original source actions remains a separate
obligation of the same source-reconstruction family. The literal quotient
application is in UnitarySource/FiveApplication.
-/

public section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveExceptional
variable {E : Type*} [Field E] [CharP E 2]
attribute [local simp] CharTwo.ofNat_eq_mod CharTwo.add_self_eq_zero

private theorem system_kernel (ω : E) (hω : ω^2=ω+1)
    (x : Fin 5 → E)
    (h0 : x 0+x 1+ω*x 3=0)
    (h1 : x 0+ω^2*x 1+x 2=0)
    (h2 : x 0+x 3+ω^2*x 4=0)
    (h3 : x 0+ω^2*x 1+ω^2*x 4=0)
    (h4 : x 0+ω^2*x 2+x 4=0) : ∀ i, x i=0 := by
  intro i
  fin_cases i
  · linear_combination (norm := (ring_nf; simp))
      h0+ω*h2+ω*h3+(ω*x 1+x 1)*hω
  · linear_combination (norm := (ring_nf; simp))
      h1+(ω+1)*h3+ω*h4+(ω*x 1+ω*x 2+ω*x 4+x 1+x 2)*hω
  · linear_combination (norm := (ring_nf; simp))
      h0+ω*h1+ω*h2+h4+(ω*x 1+ω*x 4+x 1+x 2+x 4)*hω
  · linear_combination (norm := (ring_nf; simp))
      (ω+1)*h1+h2+(ω+1)*h3+h4+(ω*x 4+x 2+x 4)*hω
  · linear_combination (norm := (ring_nf; simp))
      ω*h0+h1+(ω+1)*h2+ω*h3+ω*h4+(ω*x 1+ω*x 2+x 2+x 3+x 4)*hω

/-- Solve all five source equations (8.35) with the original coefficients. -/
theorem system_solution (ω θ : E) (hω : ω^2=ω+1) (hθ : θ^2=θ+ω)
    (x : Fin 5 → E)
    (h0 : x 0+x 1+ω*x 3=(ω*θ)^4)
    (h1 : x 0+ω^2*x 1+x 2=(ω*θ)^3+1)
    (h2 : x 0+x 3+ω^2*x 4=(ω*θ)^2+ω)
    (h3 : x 0+ω^2*x 1+ω^2*x 4=θ^4)
    (h4 : x 0+ω^2*x 2+x 4=ω^2*θ^4) : ∀ i, x i=θ+1 := by
  have hθ4 : θ^4=θ+1 := by
    calc
      θ^4=(θ+ω)^2 := by rw [←hθ]; ring
      _=θ+1 := by
        linear_combination (norm := (ring_nf; simp)) hθ+hω
  have he2 : (ω*θ)^2=(ω+1)*θ+1 := by
    rw [mul_pow,hω,hθ]
    linear_combination (norm := (ring_nf; simp)) hω
  have he3 : (ω*θ)^3=(ω+1)*θ+ω := by
    calc
      (ω*θ)^3=(ω*θ)^2*(ω*θ) := by ring
      _=((ω+1)*θ+1)*(ω*θ) := by rw [he2]
      _=(ω+1)*θ+ω := by
        linear_combination (norm := (ring_nf; simp))
          θ^2*hω+hθ
  have he4 : (ω*θ)^4=ω*(θ+1) := by
    calc
      (ω*θ)^4=((ω+1)*θ+1)^2 := by rw [←he2]; ring
      _=ω*(θ+1) := by
        linear_combination (norm := (ring_nf; simp))
          θ^2*hω+ω*hθ+hω
  rw [he4] at h0
  rw [he3] at h1
  rw [he2] at h2
  rw [hθ4] at h3 h4
  have hy : ∀ i, (fun j => x j-(θ+1)) i=0 := by
    apply system_kernel ω hω
    · linear_combination (norm := (ring_nf; simp)) h0
    · linear_combination (norm := (ring_nf; simp)) h1-(θ+1)*hω
    · linear_combination (norm := (ring_nf; simp)) h2-(θ+1)*hω
    · linear_combination (norm := (ring_nf; simp)) h3
    · linear_combination (norm := (ring_nf; simp)) h4
  intro i
  exact sub_eq_zero.mp (hy i)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveExceptional
