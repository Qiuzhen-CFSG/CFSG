module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The hyperbolic splitting code is adapted from Atlas/LinearAlgebra/SymplecticBasis.lean,
via Theory/SpecificGroups/SymplecticFour/Sylow/AmbientOrder/PairRecurrence.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt);
see LICENSES/ATLAS-CITATION.cff. Changes: a private namespace and only the
splitting identities needed for the new linear-half theorem. Originals unchanged.
-/

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Linear halves of alternating forms

Hyperbolic splitting, iterated through the possibly degenerate complement,
constructs an endomorphism z with B(zx,y) + B(x,zy) = B(x,y). No division by two
is involved. This supplies the linear equation used in the square-zero form
correction for odd-order symplectic conjugacy.

The private splitting adaptation below is from the ATLAS source named above.
It is local because the legacy CFSG port is not a Lean module.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection

noncomputable section
namespace Hyperbolic
open LinearMap
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)

variable (e f : V) (hef : B e f = 1)

/-- The simultaneous orthogonal complement of the selected hyperbolic pair. -/
def complement : Submodule F V := (B.flip e).ker ⊓ (B.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement B e f ↔ B x e = 0 ∧ B x f = 0 := Iff.rfl

/-- Projection onto the selected plane, in its normalized coordinates. -/
def planeProjection : V →ₗ[F] V := (B.flip f).smulRight e - (B.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection B e f x = (B x f) • e - (B x e) • f := rfl

include hA hef
theorem reversed_pairing : B f e = -1 := by rw [← hA.neg_eq e f, hef]

@[simp] theorem projection_e : planeProjection B e f e = e := by
  simp [planeProjection_apply, hef, hA.self_eq_zero]

@[simp] theorem projection_f : planeProjection B e f f = f := by
  simp [planeProjection_apply, reversed_pairing B hA e f hef, hA.self_eq_zero]

theorem remainder_mem (x : V) : x - planeProjection B e f x ∈ complement B e f := by
  simp only [mem_complement, planeProjection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hA.self_eq_zero,
    reversed_pairing B hA e f hef, hef]
  constructor <;> ring

/-- The hyperbolic coordinates plus the actual complement give a direct decomposition. -/
def split : V ≃ₗ[F] (F × F) × complement B e f where
  toFun x := ((B x f, -B x e), ⟨x-planeProjection B e f x, remainder_mem B hA e f hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by
    simp only [planeProjection_apply, neg_smul]
    abel
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw' := (mem_complement B e f w).mp hw
    apply Prod.ext
    · apply Prod.ext <;>
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hef, hA.self_eq_zero, reversed_pairing B hA e f hef, hw'.1, hw'.2]
    · apply Subtype.ext
      simp only [planeProjection_apply, map_add, map_smul,
        hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, add_comm]
    · apply Subtype.ext
      change x+y-planeProjection B e f (x+y) =
        (x-planeProjection B e f x)+(y-planeProjection B e f y)
      rw [map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · simp [map_smul, mul_neg]
    · apply Subtype.ext
      simp [map_smul, smul_sub]

omit hef in
/-- The alternating restriction on the actual complement. -/
theorem complement_alternating : (B.restrict (complement B e f)).IsAlt := by
  intro x
  exact hA.self_eq_zero x.val

theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement B e f) + 2 = Module.finrank F V := by
  have h := (split B hA e f hef).finrank_eq
  simpa [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm


/-- The decomposition is orthogonal and has the normalized hyperbolic plane form. -/
theorem split_form (z z' : (F × F) × complement B e f) :
    B ((split B hA e f hef).symm z) ((split B hA e f hef).symm z') =
      z.1.1*z'.1.2-z.1.2*z'.1.1+B z.2.val z'.2.val := by
  rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
  rcases z' with ⟨⟨t,u⟩,⟨v,hv⟩⟩
  have hw := (mem_complement B e f w).mp hw
  have hv := (mem_complement B e f v).mp hv
  have hev : B e v = 0 := by rw [← hA.neg_eq v e, hv.1, neg_zero]
  have hfv : B f v = 0 := by rw [← hA.neg_eq v f, hv.2, neg_zero]
  change B (r • e+s • f+w) (t • e+u • f+v) = r*u-s*t+B w v
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hA.self_eq_zero, hef, reversed_pairing B hA e f hef,
    hw.1, hw.2, hev, hfv]
  ring

end Hyperbolic

open LinearMap
open Hyperbolic

universe u v
variable {F : Type u} [Field F]

private theorem alternating_half
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hB : B.IsAlt) :
    ∃ z : V →ₗ[F] V, ∀ x y, B (z x) y + B x (z y) = B x y := by
  classical
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hzero : B = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨e, f, hef⟩ : ∃ e f, B e f ≠ 0 := by
      by_contra! hz
      exact hzero (by ext x y; exact hz x y)
    let f' := (B e f)⁻¹ • f
    have hef' : B e f' = 1 := by simp [f', hef]
    let P := complement B e f'
    have hPdim := finrank_complement B hB e f' hef'
    have hlt : Module.finrank F P < n := by dsimp only [P]; omega
    obtain ⟨z, hz⟩ := ih (Module.finrank F P) hlt
      (B.restrict P) (complement_alternating B hB e f') rfl
    let L := split B hB e f' hef'
    let Z : (F × F) × P →ₗ[F] (F × F) × P :=
      (LinearMap.fst F F F).prod (0 : (F × F) →ₗ[F] F) |>.prodMap z
    refine ⟨L.symm.toLinearMap ∘ₗ Z ∘ₗ L.toLinearMap, ?_⟩
    intro x y
    obtain ⟨x, rfl⟩ := L.symm.surjective x
    obtain ⟨y, rfl⟩ := L.symm.surjective y
    change B (L.symm (Z (L (L.symm x)))) (L.symm y) +
      B (L.symm x) (L.symm (Z (L (L.symm y)))) = B (L.symm x) (L.symm y)
    simp only [L.apply_symm_apply]
    change B (L.symm ((x.1.1, 0), z x.2)) (L.symm y) +
      B (L.symm x) (L.symm ((y.1.1, 0), z y.2)) = B (L.symm x) (L.symm y)
    dsimp only [L]
    rw [split_form, split_form, split_form]
    have h := hz x.2 y.2
    change B (z x.2).val y.2.val + B x.2.val (z y.2).val = B x.2.val y.2.val at h
    simp only [mul_zero, zero_mul, sub_zero, zero_sub]
    linear_combination h

/-- An alternating matrix, including a degenerate one, admits a linear half. -/
public theorem exists_alternating_half {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n F) (hA : A.toBilin'.IsAlt) :
    ∃ Z : Matrix n n F, Z.transpose * A + A * Z = A := by
  obtain ⟨z, hz⟩ := alternating_half A.toBilin' hA
  refine ⟨LinearMap.toMatrix' z, ?_⟩
  have he : A.toBilin'.compLeft z + A.toBilin'.compRight z = A.toBilin' := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hz x y
  have hm := congrArg LinearMap.BilinForm.toMatrix' he
  simpa only [map_add, LinearMap.BilinForm.toMatrix'_compLeft, LinearMap.BilinForm.toMatrix'_compRight,
    LinearMap.BilinForm.toMatrix'_toBilin'] using hm
end

end Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection
