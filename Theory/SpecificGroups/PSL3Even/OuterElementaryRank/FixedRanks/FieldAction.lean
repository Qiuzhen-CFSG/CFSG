module

public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Group

/-!
# Detecting the coefficient involution in actual PSL₃ actions

A field automorphism which acts by linear conjugation on PSL₃ is trivial.
Perfectness lifts equality of projective actors to SL₃, where conjugation
preserves trace and determinant-one companion matrices realize every trace.
Squaring the literal linear–field and linear–field–graph expressions then
shows that an involutory actor has involutory coefficient action.

This supplies the field parameter needed before fixed-group descent; it
assumes no normal-form uniqueness or conjugacy classification. Source: GLS3,
Theorem 2.5.12(d) and §2.7. The trace argument parallels
`Theory/SpecificGroups/SL2/FieldAutomorphismCore.lean`; perfectness is reused
from the attributed ATLAS port `ExceptionalIsomorphisms.Elementary`.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks
variable {F : Type*} [Field F]
/-- Coefficient transport is linear only for the identity field automorphism. -/
theorem field_eq_one_of_linear (σ : F ≃+* F) (g : GL (Fin 3) F)
    (h : fieldAction F σ = linearConj F g) : σ = 1 := by
  have he : Atlas.fieldEquivSL 3 σ = linearConjSL F g := by
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    apply MulAut.quotient_center_injective
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
    rw [Subgroup.quotientAut_apply_mk, Subgroup.quotientAut_apply_mk]
    have hx := MulEquiv.congr_fun h (QuotientGroup.mk y)
    rw [fieldAction_mk, linearConj_mk] at hx
    exact hx
  ext t
  let x : SL(3,F) := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, t], by simp [Matrix.det_fin_three]⟩
  have ht := congrArg (fun y : GL (Fin 3) F => Matrix.trace y.val)
    (congrArg SpecialLinearGroup.toGL (MulEquiv.congr_fun he x))
  rw [linearConjSL_toGL] at ht
  change Matrix.trace (x.val.map σ) = Matrix.trace (g.val * x.val * g.inv) at ht
  have ht' := ht.trans (Matrix.trace_units_conj g x.val)
  simpa [Matrix.trace, Fin.sum_univ_three, x] using ht'

/-- Square the literal semilinear projective action. -/
theorem linear_field_sq (g : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F g * fieldAction F σ) ^ 2 =
      linearConj F (g * GeneralLinearGroup.map σ.toRingHom g) * fieldAction F (σ ^ 2) := by
  rw [pow_two, mul_assoc, ← mul_assoc (fieldAction F σ), field_linearConj,
    mul_assoc, ← mul_assoc (linearConj F g), ← map_mul]
  rw [← pow_two, ← map_pow]

/-- Square the literal graph-field projective action, including its linear twist. -/
theorem graphField_sq (g : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F g * fieldAction F σ * graph F) ^ 2 =
      linearConj F (g * GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F g)) *
        fieldAction F (σ ^ 2) := by
  calc
    _ = linearConj F g * fieldAction F σ *
        (graph F * linearConj F g) * fieldAction F σ * graph F := by
          simp only [pow_two, mul_assoc]
    _ = linearConj F g *
        (fieldAction F σ * linearConj F (inverseTransposeGL F g)) *
        (graph F * fieldAction F σ) * graph F := by rw [graph_linearConj]; group
    _ = linearConj F g *
        (linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F g)) *
          fieldAction F σ) * (fieldAction F σ * graph F) * graph F := by
      rw [field_linearConj, ← (field_commute_graph σ).eq]
    _ = (linearConj F g *
        linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F g))) *
        (fieldAction F σ * fieldAction F σ) * (graph F * graph F) := by group
    _ = _ := by rw [← map_mul, ← pow_two, ← map_pow, ← pow_two, graph_sq, mul_one]

private theorem field_eq_one_of_linear_mul (g : GL (Fin 3) F) (σ : F ≃+* F)
    (h : linearConj F g * fieldAction F σ = 1) : σ = 1 := by
  apply field_eq_one_of_linear σ g⁻¹
  rw [map_inv]
  exact eq_inv_of_mul_eq_one_right h

/-- An involutory semilinear actor has coefficient action of order dividing two. -/
theorem field_part_sq (g : GL (Fin 3) F) (σ : F ≃+* F)
    (h : (linearConj F g * fieldAction F σ) ^ 2 = 1) : σ ^ 2 = 1 := by
  rw [linear_field_sq] at h
  exact field_eq_one_of_linear_mul _ _ h

/-- An involutory graph-field actor has coefficient action of order dividing two. -/
theorem graphField_part_sq (g : GL (Fin 3) F) (σ : F ≃+* F)
    (h : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) : σ ^ 2 = 1 := by
  rw [graphField_sq] at h
  exact field_eq_one_of_linear_mul _ _ h
end Matrix.PSL3Even.OuterElementaryRank.FixedRanks
