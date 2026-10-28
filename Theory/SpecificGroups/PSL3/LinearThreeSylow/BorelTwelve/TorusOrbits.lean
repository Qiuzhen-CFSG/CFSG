module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Large unipotent orbits of nontrivial diagonal elements in PSL₃

The three root characters of a diagonal matrix satisfy α₁₃ = α₁₂α₂₃.
If both simple-root characters are trivial, the matrix is a cubic scalar,
so its projective image is the identity. Thus a nonidentity torus element
has two nontrivial root characters. Varying the corresponding two coordinates
of the upper-unitriangular group gives |F|² distinct conjugates.

Consequently a subgroup normalized by the unipotent group and containing
such an element has order at least |F|². The calculation uses the faithful
projective realization of the existing unitriangular matrix model, retaining
the full cubic scalar kernel.

Source: the intrinsic PSL₃ Borel assertion in Aschbacher–Smith, E.6.8,
printed p.248 (combined manuscript, 1 March 2004).
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.BorelTwelve
variable (F : Type*) [Field F]
private def root₁ (d : Fˣ × Fˣ) : Fˣ := d.1 * (d.1 * d.2)
private def root₂ (d : Fˣ × Fˣ) : Fˣ := (d.1 * d.2)⁻¹ * d.2⁻¹
private def root₃ (d : Fˣ × Fˣ) : Fˣ := d.1 * d.2⁻¹
private theorem root_product (d : Fˣ × Fˣ) : root₁ F d * root₂ F d = root₃ F d := by
  simp [root₁, root₂, root₃, mul_assoc]
private theorem roots_trivial (d : Fˣ × Fˣ) (h₁ : root₁ F d = 1)
    (h₂ : root₂ F d = 1) : torusMap F d = 1 := by
  have h₃ : root₃ F d = 1 := by rw [← root_product, h₁, h₂, one_mul]
  have hab : d.1 = d.2 := mul_inv_eq_one.mp h₃
  apply (BorelQuotient.torusMap_eq_one_iff F d).mpr
  refine ⟨hab, ?_⟩
  simpa [root₁, ← hab, pow_succ, mul_assoc] using h₁
private theorem torus_conj (d : Fˣ × Fˣ) (u : U F) :
    torusMap F d * projective F u * (torusMap F d)⁻¹ =
      projective F ⟨root₁ F d * u.x, root₂ F d * u.y, root₃ F d * u.c⟩ := by
  change projection F (torusSL F d) * projection F (specialLinear F u) *
    (projection F (torusSL F d))⁻¹ = projection F (specialLinear F _)
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (projection F)
  rw [← map_inv]
  apply Subtype.ext
  change (torusSL F d).val * matrix F u * (torusSL F d⁻¹).val =
    matrix F ⟨root₁ F d * u.x, root₂ F d * u.y, root₃ F d * u.c⟩
  rw [torusSL_val, torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, root₁, root₂, root₃, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_assoc, mul_left_comm, mul_comm]
  all_goals field_simp
private theorem conjugate_difference (d : Fˣ × Fˣ) (u : U F) :
    projective F u * torusMap F d * (projective F u)⁻¹ * (torusMap F d)⁻¹ =
      projective F (u * (⟨root₁ F d * u.x, root₂ F d * u.y, root₃ F d * u.c⟩ : U F)⁻¹) := by
  rw [map_mul, map_inv, ← torus_conj]
  group

private theorem conjugates_eq (d : Fˣ × Fˣ) {u v : U F}
    (h : projective F u * torusMap F d * (projective F u)⁻¹ =
      projective F v * torusMap F d * (projective F v)⁻¹) :
    u * (⟨root₁ F d * u.x, root₂ F d * u.y, root₃ F d * u.c⟩ : U F)⁻¹ =
      v * (⟨root₁ F d * v.x, root₂ F d * v.y, root₃ F d * v.c⟩ : U F)⁻¹ := by
  apply projective_injective F
  rw [← conjugate_difference, ← conjugate_difference, h]

private theorem sub_mul_cancel {a x y : F} (ha : a ≠ 1)
    (h : x + -(a * x) = y + -(a * y)) : x = y := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr ha)
  linear_combination -h

private theorem two_parameter_conjugates (d : Fˣ × Fˣ) (hd : torusMap F d ≠ 1) :
    ∃ f : F × F → U F, Function.Injective
      (fun p => projective F (f p) * torusMap F d * (projective F (f p))⁻¹) := by
  classical
  have hval {r : Fˣ} (hr : r ≠ 1) : (r : F) ≠ 1 := by
    intro he
    exact hr (Units.ext he)
  by_cases h₁ : root₁ F d = 1
  · have h₂ : root₂ F d ≠ 1 := fun h₂ => hd (roots_trivial F d h₁ h₂)
    have h₃ : root₃ F d ≠ 1 := by rwa [← root_product, h₁, one_mul]
    refine ⟨fun p => ⟨0,p.1,p.2⟩, ?_⟩
    intro p q he
    have hc := conjugates_eq F d he
    have hy := congrArg U.y hc
    have hz := congrArg U.c hc
    apply Prod.ext
    · exact sub_mul_cancel F (hval h₂) hy
    · apply sub_mul_cancel F (hval h₃)
      simpa [mul_c, Inv.inv] using hz
  · by_cases h₂ : root₂ F d = 1
    · have h₃ : root₃ F d ≠ 1 := by rwa [← root_product, h₂, mul_one]
      refine ⟨fun p => ⟨p.1,0,p.2⟩, ?_⟩
      intro p q he
      have hc := conjugates_eq F d he
      have hx := congrArg U.x hc
      have hz := congrArg U.c hc
      apply Prod.ext
      · exact sub_mul_cancel F (hval h₁) hx
      · apply sub_mul_cancel F (hval h₃)
        simpa [mul_c, Inv.inv] using hz
    · refine ⟨fun p => ⟨p.1,p.2,0⟩, ?_⟩
      intro p q he
      have hc := conjugates_eq F d he
      exact Prod.ext (sub_mul_cancel F (hval h₁) (congrArg U.x hc))
        (sub_mul_cancel F (hval h₂) (congrArg U.y hc))

/-- A nonidentity diagonal element has at least q² conjugates under U.
All of these lie in any subgroup normalized by U and containing that element. -/
theorem card_sq_le_of_torus_mem [Finite F] (H : Subgroup PSL(3,F))
    (hU : unipotent F ≤ normalizer H) (d : Fˣ × Fˣ)
    (hd : torusMap F d ∈ H) (hd1 : torusMap F d ≠ 1) : Nat.card F ^ 2 ≤ Nat.card H := by
  obtain ⟨f,hf⟩ := two_parameter_conjugates F d hd1
  have hu (u : U F) : projective F u ∈ unipotent F :=
    (projective_range F).le ⟨u,rfl⟩
  let g : F × F → H := fun p =>
    ⟨projective F (f p) * torusMap F d * (projective F (f p))⁻¹,
      (mem_normalizer_iff.mp (hU (hu (f p))) _).mp hd⟩
  have hg : Function.Injective g := fun p q he => hf (congrArg Subtype.val he)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective g hg

end Matrix.PSL3.LinearThree.BorelTwelve
