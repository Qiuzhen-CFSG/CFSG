module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Mathlib.Tactic.Group

/-!
# Involution fusion in the projective field coset

The existing matrix Sylow model is UT₃(4) extended by Frobenius. An
involution in its field coset satisfies a unitriangular cocycle equation.
The two adjacent coordinates are Frobenius fixed. Surjectivity of the
scalar trace onto the fixed field solves those coordinates and then the
central coordinate. Hence every such cocycle is a coboundary.

Sylow conjugacy covers all involutions in the full field extension. Removing
the field component of its conjugator retains a conjugator in the actual
PSL₃(4). The final cocycle statement uses the original entrywise Frobenius,
with no change to either the projective quotient or its matrix embedding.
Source: Aschbacher--Smith 15.3.38, printed p.1137, manuscript of 1 March 2004.
-/

public section

namespace Matrix.PSL3Four.InvolutionClasses
open SylowModel

private theorem exists_trace (x : F) (hx : fieldFrobenius x = x) :
    ∃ y : F, SylowModel.trace y = x := by
  refine ⟨omega * x, ?_⟩
  simp only [SylowModel.trace, map_mul, hx, omega_frobenius]
  calc
    omega * x + (omega + 1) * x = (omega + omega) * x + x := by ring
    _ = x := by rw [CharTwo.add_self_eq_zero, zero_mul, zero_add]

private theorem unipotent_coboundary (u : U) (hu : u * frob u = 1) :
    ∃ b : U, u = b * (frob b)⁻¹ := by
  have hx : fieldFrobenius u.x = u.x := by
    have h := congrArg U.x hu
    change u.x + fieldFrobenius u.x = 0 at h
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left h).symm
  have hy : fieldFrobenius u.y = u.y := by
    have h := congrArg U.y hu
    change u.y + fieldFrobenius u.y = 0 at h
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left h).symm
  have hc : SylowModel.trace u.c = u.x * u.y := by
    have h := congrArg U.c hu
    change u.c + fieldFrobenius u.c + u.x * fieldFrobenius u.y = 0 at h
    rw [hy] at h
    simpa only [SylowModel.trace, CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
  obtain ⟨a, ha⟩ := exists_trace u.x hx
  obtain ⟨b, hb⟩ := exists_trace u.y hy
  have ht : SylowModel.trace (u.c + u.x * fieldFrobenius b) = 0 := by
    rw [SylowModel.trace_add, hc]
    have hm : SylowModel.trace (u.x * fieldFrobenius b) = u.x * SylowModel.trace b := by
      simp only [SylowModel.trace, map_mul, hx, fieldFrobenius_involutive]
      ring
    rw [hm, hb, CharTwo.add_self_eq_zero]
  obtain ⟨d, hd⟩ := exists_trace _ ((SylowModel.trace_eq_zero _).mp ht)
  refine ⟨⟨a,b,d⟩, (eq_mul_inv_iff_mul_eq).mpr ?_⟩
  apply U.ext
  · change u.x + fieldFrobenius a = a
    rw [← ha]
    simp only [SylowModel.trace, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · change u.y + fieldFrobenius b = b
    rw [← hb]
    simp only [SylowModel.trace, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · change u.c + fieldFrobenius d + u.x * fieldFrobenius b = d
    calc
      _ = (u.c + u.x * fieldFrobenius b) + fieldFrobenius d := by ring
      _ = SylowModel.trace d + fieldFrobenius d := by rw [hd]
      _ = d := by simp only [SylowModel.trace, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem sylow_field_conjugate (u : T) (hu : u ^ 2 = 1) (hr : u.right = τ) :
    ∃ b : U, inclusion b * (SemidirectProduct.inr τ : T) * (inclusion b)⁻¹ = u := by
  have hc : u.left * frob u.left = 1 := by
    have h := congrArg (fun x : T => x.left) hu
    simpa only [pow_two, SemidirectProduct.mul_left, hr, action_τ,
      SemidirectProduct.one_left] using h
  obtain ⟨b, hb⟩ := unipotent_coboundary u.left hc
  refine ⟨b, ?_⟩
  apply SemidirectProduct.ext
  · simpa [inclusion, action_τ, map_inv] using hb.symm
  · simpa [inclusion] using hr.symm

end Matrix.PSL3Four.InvolutionClasses

namespace Matrix.PSL3Four.InvolutionClasses
open Subgroup SylowModel
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

private theorem linear_conjugation_field (a : FieldExtension) :
    a * fieldInclusion τ * a⁻¹ =
      linearInclusion a.left * fieldInclusion τ * (linearInclusion a.left)⁻¹ := by
  have hcomm : fieldInclusion a.right * fieldInclusion τ * (fieldInclusion a.right)⁻¹ =
      fieldInclusion τ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm a.right, mul_inv_cancel_right]
  calc
    _ = linearInclusion a.left *
        (fieldInclusion a.right * fieldInclusion τ * (fieldInclusion a.right)⁻¹) *
        (linearInclusion a.left)⁻¹ := by
          conv_lhs => rw [← linear_mul_field a]
          group
    _ = _ := by rw [hcomm]

/-- Every involution in the actual projective field coset is linearly conjugate to Frobenius. -/
theorem projective_field_coset_conjugate (x : FieldExtension)
    (hx : x ^ 2 = 1) (hr : x.right = τ) :
    ∃ b : PSL, linearInclusion b * fieldInclusion τ * (linearInclusion b)⁻¹ = x := by
  obtain ⟨a, ha⟩ := conjugate_mem_sylow MatrixRealization.sylow x hx
  obtain ⟨u, hu⟩ := ha
  have hu2 : u ^ 2 = 1 := by
    apply MatrixRealization.embedding_injective
    rw [map_pow, map_one, hu]
    calc
      (a * x * a⁻¹) ^ 2 = a * x ^ 2 * a⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; simp
  have hur : u.right = τ := by
    have h := congrArg fieldProjection hu
    change u.right = fieldProjection (a * x * a⁻¹) at h
    rw [map_mul, map_mul, map_inv] at h
    change u.right = a.right * x.right * a.right⁻¹ at h
    simpa only [hr, mul_comm a.right, mul_inv_cancel_right] using h
  obtain ⟨b, hb⟩ := sylow_field_conjugate u hu2 hur
  have he : MatrixRealization.embedding (SemidirectProduct.inr τ) = fieldInclusion τ := by
    simp [MatrixRealization.embedding, fieldInclusion]
  have hb' : linearInclusion (MatrixRealization.projective b) * fieldInclusion τ *
      (linearInclusion (MatrixRealization.projective b))⁻¹ = a * x * a⁻¹ := by
    simpa only [map_mul, map_inv, MatrixRealization.embedding_inclusion, he] using
      (congrArg MatrixRealization.embedding hb).trans hu
  let k := a⁻¹ * linearInclusion (MatrixRealization.projective b)
  refine ⟨k.left, ?_⟩
  rw [← linear_conjugation_field k]
  calc
    k * fieldInclusion τ * k⁻¹ = a⁻¹ *
        (linearInclusion (MatrixRealization.projective b) * fieldInclusion τ *
          (linearInclusion (MatrixRealization.projective b))⁻¹) * a := by dsimp [k]; group
    _ = x := by rw [hb']; group

/-- The projective Frobenius cocycle equation has only coboundaries. -/
theorem projective_field_coboundary (x : PSL) (hx : x * pslFrobenius x = 1) :
    ∃ b : PSL, x = b * (pslFrobenius b)⁻¹ := by
  let y : FieldExtension := ⟨x, τ⟩
  have hy : y ^ 2 = 1 := by
    apply SemidirectProduct.ext
    · simpa only [pow_two, SemidirectProduct.mul_left, y, τ, fieldAction_generator, SemidirectProduct.one_left] using hx
    · change (τ * τ : C2) = 1
      decide
  obtain ⟨b, hb⟩ := projective_field_coset_conjugate y hy rfl
  refine ⟨b, ?_⟩
  have h := congrArg (fun z : FieldExtension => z.left) hb
  simpa [linearInclusion, fieldInclusion, fieldAction_generator, map_inv, y, τ] using h.symm

end Matrix.PSL3Four.InvolutionClasses
