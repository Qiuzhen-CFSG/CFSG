module

public import Theory.SpecificGroups.PSL3Four.CentralCover
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Mathlib.GroupTheory.Sylow

/-!
# Coverage of four-cover involutions by the central root preimage

The unitriangular subgroup has the full two-part of |PSL₃(4)|. Every
involution is conjugate into it; its two adjacent entries have product zero.
Explicit determinant-one row and column operations then conjugate it into
the highest-root group. Surjectivity of a cover lifts the conjugator, and
containment of its central kernel puts the lift in the given root preimage.
The root marking may be any inner conjugate of the standard one.

This proves the coverage assertion used in Aschbacher--Smith 15.3.38,
printed p.1137 (combined manuscript of 1 March 2004). Fusion among the
representatives in the source V is separate ambient geometry. In particular,
distinct central elements remain distinct conjugacy classes in the cover.
-/

public section

open Matrix
namespace Matrix.PSL3Four.InvolutionClasses
open PSL3Even.UnipotentGeometry

private theorem unitriangular_conjugate_root (a : U F) (ha : a ^ 2 = 1) :
    ∃ b : SL, ∃ t : F, b * specialLinear F a * b⁻¹ = specialLinear F ⟨0,0,t⟩ := by
  rcases a with ⟨x,y,c⟩
  rcases (square_eq_one_iff F _).mp ha with h | h
  · change x = 0 at h
    subst x
    by_cases hc : c = 0
    · subst c
      let b : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by
        simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
      refine ⟨b, y, (mul_inv_eq_iff_eq_mul).mpr ?_⟩
      apply Subtype.ext
      change b.val * matrix F ⟨0,y,0⟩ = matrix F ⟨0,0,y⟩ * b.val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b, matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · let b : SL := ⟨!![1,0,0; y/c,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩
      refine ⟨b, c, (mul_inv_eq_iff_eq_mul).mpr ?_⟩
      apply Subtype.ext
      change b.val * matrix F ⟨0,y,c⟩ = matrix F ⟨0,0,c⟩ * b.val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b, matrix, Matrix.mul_apply, Fin.sum_univ_three, hc,
          CharTwo.add_self_eq_zero]
  · change y = 0 at h
    subst y
    by_cases hc : c = 0
    · subst c
      let b : SL := ⟨!![1,0,0; 0,0,1; 0,1,0], by
        simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
      refine ⟨b, x, (mul_inv_eq_iff_eq_mul).mpr ?_⟩
      apply Subtype.ext
      change b.val * matrix F ⟨x,0,0⟩ = matrix F ⟨0,0,x⟩ * b.val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b, matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · let b : SL := ⟨!![1,0,0; 0,1,0; 0,x/c,1], by simp [Matrix.det_fin_three]⟩
      refine ⟨b, c, (mul_inv_eq_iff_eq_mul).mpr ?_⟩
      apply Subtype.ext
      change b.val * matrix F ⟨x,0,c⟩ = matrix F ⟨0,0,c⟩ * b.val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b, matrix, Matrix.mul_apply, Fin.sum_univ_three, hc,
          CharTwo.add_self_eq_zero, mul_div_cancel₀]

open Subgroup
open scoped Pointwise

private theorem conjugate_mem_sylow {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (x : H) (hx : x ^ 2 = 1) :
    ∃ b : H, b * x * b⁻¹ ∈ P := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx
  obtain ⟨Q, hQ⟩ := (IsElementaryAbelian.isPGroup 2 (zpowers x)).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨b, ?_⟩
  rw [← hb]
  exact smul_mem_pointwise_smul x (MulAut.conj b) (Q : Subgroup H) (hQ (mem_zpowers x))

private noncomputable def projectiveSylow : Sylow 2 PSL :=
  Sylow.ofCard (projective F).range (by
    rw [projective_range_card, card_F, card_PSL]
    decide +kernel)

theorem projective_conjugate_root (x : PSL) (hx : x ^ 2 = 1) :
    ∃ b : PSL, b * x * b⁻¹ ∈ projectiveCenter F := by
  obtain ⟨b, hb⟩ := conjugate_mem_sylow projectiveSylow x hx
  obtain ⟨u, hu⟩ := hb
  have hu2 : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, map_one, hu]
    calc
      (b * x * b⁻¹) ^ 2 = b * x ^ 2 * b⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; simp
  obtain ⟨a, t, ht⟩ := unitriangular_conjugate_root u hu2
  have ht' : (a : PSL) * projective F u * (a : PSL)⁻¹ = projective F ⟨0,0,t⟩ :=
    congrArg (QuotientGroup.mk' (center SL)) ht
  refine ⟨(a : PSL) * b, ?_⟩
  apply (mem_projectiveCenter F _).mpr
  refine ⟨t, ?_⟩
  rw [← ht', hu]
  group

/-- The full inverse image of a root contains a conjugate of each element of square one. -/
theorem cover_conjugate_into {E : Type*} [Group E]
    (c : FourCover E) (V : Subgroup E) (hZ : center E ≤ V)
    (g : PSL) (hroot : (projectiveCenter F).map (MulAut.conj g).toMonoidHom ≤
      V.map c.toMonoidHom) (x : E) (hx : x ^ 2 = 1) :
    ∃ b : E, b * x * b⁻¹ ∈ V := by
  obtain ⟨b, hb⟩ := projective_conjugate_root (c.toMonoidHom x)
    (by rw [← map_pow, hx, map_one])
  obtain ⟨a, ha⟩ := c.surjective (g * b)
  have hmem : c.toMonoidHom (a * x * a⁻¹) ∈ V.map c.toMonoidHom := by
    apply hroot
    refine ⟨b * c.toMonoidHom x * b⁻¹, hb, ?_⟩
    change g * (b * c.toMonoidHom x * b⁻¹) * g⁻¹ = c.toMonoidHom (a * x * a⁻¹)
    rw [map_mul, map_mul, map_inv, ha]
    group
  obtain ⟨v, hv, he⟩ := hmem
  have hk : a * x * a⁻¹ * v⁻¹ ∈ c.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hz : a * x * a⁻¹ * v⁻¹ ∈ V := hZ (c.ker_eq_center ▸ hk)
  exact ⟨a, by simpa using V.mul_mem hz hv⟩

/-- Central elements are never identified by conjugation inside the cover. -/
theorem central_isConj_iff {E : Type*} [Group E]
    (z w : center E) : IsConj (z : E) (w : E) ↔ z = w := by
  constructor
  · intro h
    exact Subtype.ext (h.eq_of_left_mem_center z.property)
  · rintro rfl
    exact IsConj.refl _

end Matrix.PSL3Four.InvolutionClasses
