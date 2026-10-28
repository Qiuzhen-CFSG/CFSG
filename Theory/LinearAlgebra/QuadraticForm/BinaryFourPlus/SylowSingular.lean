module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# Singular spaces invariant under a Sylow subgroup of O₄⁺(2)

An isometry reflecting one anisotropic plane has nonsingular displacement.
Hence every invariant totally singular space is fixed pointwise by that
reflection, and its fixed singular vectors contain no singular plane.
The finite verification uses at most pairs of the sixteen original vectors.
Sylow conjugacy transports the bound to every Sylow two-subgroup of the
full orthogonal group, preserving the original linear action.

This is the finite orthogonal fact used to identify E=V in
Aschbacher--Smith 14.3.18(1), printed pp.995--996.
-/

namespace BinaryFourPlus
open Subgroup

private def axisReflectionLinear : V ≃ₗ[ZMod 2] V where
  toFun v := (![v.1 1, v.1 0], v.2)
  invFun v := (![v.1 1, v.1 0], v.2)
  left_inv v := by apply Prod.ext; ext i; fin_cases i <;> rfl; rfl
  right_inv v := by apply Prod.ext; ext i; fin_cases i <;> rfl; rfl
  map_add' v w := by apply Prod.ext; ext i; fin_cases i <;> rfl; rfl
  map_smul' a v := by apply Prod.ext; ext i; fin_cases i <;> rfl; rfl

private theorem axisReflection_preserves : ∀ v, q (axisReflectionLinear v) = q v := by decide

private def axisReflection : q.isometrySubgroup := ⟨axisReflectionLinear,
  (QuadraticMap.mem_isometrySubgroup q _).mpr axisReflection_preserves⟩

private theorem axisReflection_square : axisReflection ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact (by decide : ∀ v : V, axisReflectionLinear (axisReflectionLinear v) = v)

private theorem reflection_displacement : ∀ v : V,
    q (axisReflectionLinear v + v) = 0 → axisReflectionLinear v = v := by decide

set_option synthInstance.maxSize 512 in
private theorem reflection_fixed_pair : ∀ v w : V,
    q v = 0 → q w = 0 → q (v + w) = 0 →
    axisReflectionLinear v = v → axisReflectionLinear w = w →
    v = 0 ∨ w = 0 ∨ v = w := by
  have hc : ∀ v w : V,
      (q v = 0 ∧ q w = 0 ∧ q (v+w) = 0 ∧
        axisReflectionLinear v = v ∧ axisReflectionLinear w = w) →
      v = 0 ∨ w = 0 ∨ v = w := by decide
  intro v w h₁ h₂ h₃ h₄ h₅
  exact hc v w ⟨h₁, h₂, h₃, h₄, h₅⟩

private theorem singular_reflection_invariant_finrank (S : Submodule (ZMod 2) V)
    (hs : ∀ v ∈ S, q v = 0)
    (hr : ∀ v ∈ S, axisReflectionLinear v ∈ S) :
    Module.finrank (ZMod 2) S ≤ 1 := by
  have hfix (v : V) (hv : v ∈ S) : axisReflectionLinear v = v :=
    reflection_displacement v (hs _ (S.add_mem (hr v hv) hv))
  by_cases he : S = ⊥
  · rw [he, finrank_bot]
    decide
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    apply finrank_le_one (⟨v, hv⟩ : S)
    intro w
    rcases reflection_fixed_pair v w (hs v hv) (hs w w.property)
      (hs _ (S.add_mem hv w.property)) (hfix v hv) (hfix w w.property) with h | h | h
    · exact (hv0 h).elim
    · exact ⟨0, Subtype.ext (by simpa using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa using h)⟩

/-- A Sylow two-subgroup preserves only singular spaces of dimension at most one. -/
public theorem sylow_singular_invariant_finrank (T : Sylow 2 q.isometrySubgroup)
    (S : Submodule (ZMod 2) V) (hs : ∀ v ∈ S, q v = 0)
    (hi : ∀ t : T, ∀ v ∈ S, t.val.val v ∈ S) :
    Module.finrank (ZMod 2) S ≤ 1 := by
  let : Finite q.isometrySubgroup := Finite.of_equiv Wreath isometryEquivWreath.symm.toEquiv
  have hp : IsPGroup 2 (zpowers axisReflection) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      apply orderOf_eq_prime axisReflection_square
      intro he
      have hv := congrArg (fun f : q.isometrySubgroup => f.val (![1,0], 0)) he
      have : (0 : ZMod 2) = 1 := congrArg (fun v : V => v.1 0) hv
      exact zero_ne_one this)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq q.isometrySubgroup P T
  have ht : g * axisReflection * g⁻¹ ∈ (T : Subgroup q.isometrySubgroup) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hP (mem_zpowers axisReflection))
  let S' := S.map g.val.symm.toLinearMap
  have hsg (v : V) : q (g.val.symm v) = q v :=
    (QuadraticMap.mem_isometrySubgroup q _).mp (g⁻¹).property v
  have hs' : ∀ v ∈ S', q v = 0 := by
    rintro v ⟨w, hw, rfl⟩
    exact (hsg w).trans (hs w hw)
  have hr' : ∀ v ∈ S', axisReflectionLinear v ∈ S' := by
    rintro v ⟨w, hw, rfl⟩
    refine ⟨(g * axisReflection * g⁻¹).val w, hi ⟨_, ht⟩ w hw, ?_⟩
    change g.val.symm (g.val (axisReflectionLinear (g.val.symm w))) = _
    exact g.val.symm_apply_apply _
  have hh := singular_reflection_invariant_finrank S' hs' hr'
  rwa [LinearEquiv.finrank_map_eq] at hh
end BinaryFourPlus
