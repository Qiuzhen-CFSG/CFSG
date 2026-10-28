/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.KleinianIsometries
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# MonomialIsometries

Coordinate permutations with local Kleinian isometries form a group acting linearly on
words. The coordinate formula proves the group laws and preservation of weight and polar
forms, then restricts the action to a code stabilizer.

Source: `Atlas/Codes/MonomialIsometries.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

/-- Local maps are indexed by destination coordinates. -/
@[ext] structure Monomial (I : Type*) where
  perm : Equiv.Perm I
  localMap : I → KIsometry

namespace Monomial
variable {I : Type*}
instance : One (Monomial I) := ⟨⟨1, fun _ => 1⟩⟩
instance : Mul (Monomial I) := ⟨fun g h => ⟨g.perm * h.perm,
  fun i => g.localMap i * h.localMap (g.perm.symm i)⟩⟩
instance : Inv (Monomial I) := ⟨fun g => ⟨g.perm⁻¹,
  fun i => (g.localMap (g.perm i))⁻¹⟩⟩

@[simp] theorem one_perm : (1 : Monomial I).perm = 1 := rfl
@[simp] theorem one_local (i : I) : (1 : Monomial I).localMap i = 1 := rfl
@[simp] theorem mul_perm (g h : Monomial I) : (g*h).perm = g.perm*h.perm := rfl
@[simp] theorem mul_local (g h : Monomial I) (i : I) :
    (g*h).localMap i = g.localMap i * h.localMap (g.perm.symm i) := rfl
@[simp] theorem inv_perm (g : Monomial I) : g⁻¹.perm = g.perm⁻¹ := rfl
@[simp] theorem inv_local (g : Monomial I) (i : I) :
    g⁻¹.localMap i = (g.localMap (g.perm i))⁻¹ := rfl

instance : Group (Monomial I) where
  mul_assoc g h k := by
    apply Monomial.ext
    · exact mul_assoc _ _ _
    · funext i; simp [mul_assoc, Equiv.Perm.mul_def]
  one_mul g := by
    apply Monomial.ext
    · exact one_mul g.perm
    · funext i; exact one_mul (g.localMap i)
  mul_one g := by
    apply Monomial.ext
    · exact mul_one g.perm
    · funext i; simp
  inv_mul_cancel g := by
    apply Monomial.ext
    · exact inv_mul_cancel g.perm
    · funext i; exact inv_mul_cancel (g.localMap (g.perm i))

instance [Finite I] : Finite (Monomial I) :=
  Finite.of_injective (fun g : Monomial I => (g.perm,g.localMap))
    (by intro g h e; exact Monomial.ext (Prod.mk.inj e).1 (Prod.mk.inj e).2)

def coordinateHom : Monomial I →* Equiv.Perm I where
  toFun := perm
  map_one' := rfl
  map_mul' _ _ := rfl

def act (g : Monomial I) : (I → K) ≃ₗ[Bit] (I → K) where
  toFun w i := g.localMap i (w (g.perm.symm i))
  invFun w i := (g.localMap (g.perm i)).symm (w (g.perm i))
  left_inv := by intro w; funext i; simp
  right_inv := by intro w; funext i; simp
  map_add' := by intros; funext i; simp
  map_smul' := by intros; funext i; simp

@[simp] theorem act_apply (g : Monomial I) (w : I → K) (i : I) :
    act g w i = g.localMap i (w (g.perm.symm i)) := rfl
@[simp] theorem act_one (w : I → K) : act 1 w = w := rfl
@[simp] theorem act_mul (g h : Monomial I) (w : I → K) : act (g*h) w = act g (act h w) := rfl

def linearHom : Monomial I →* ((I → K) ≃ₗ[Bit] (I → K)) where
  toFun := act
  map_one' := rfl
  map_mul' _ _ := by apply LinearEquiv.ext; intro w; rfl

theorem act_weight [Fintype I] (g : Monomial I) (w : I → K) :
    hammingNorm (act g w) = hammingNorm w := by
  classical
  simp only [hammingNorm_eq_sum, act_apply, LinearEquiv.map_eq_zero_iff]
  exact Equiv.sum_comp g.perm.symm (fun i => if w i = 0 then 0 else 1)

theorem act_quadratic [Fintype I] (g : Monomial I) (w : I → K) :
    wordQ qK (act g w) = wordQ qK w := by
  simp only [wordQ, act_apply, KIsometry.map_q]
  exact Equiv.sum_comp g.perm.symm (fun i => qK (w i))

theorem act_polar [Fintype I] (g : Monomial I) (u v : I → K) :
    wordPolar (act g u) (act g v) = wordPolar u v := by
  simp only [wordPolar_apply, act_apply, KIsometry.map_polar]
  exact Equiv.sum_comp g.perm.symm (fun i => polar (u i) (v i))

/-- The full monomial stabilizer of a given binary-linear code. -/
def stabilizer (C : Submodule Bit (I → K)) : Subgroup (Monomial I) where
  carrier := {g | ∀ w, w ∈ C ↔ act g w ∈ C}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh w; rw [act_mul, ← hg, ← hh]
  inv_mem' := by
    intro g hg w
    have hh := hg (act g⁻¹ w)
    rw [← act_mul, mul_inv_cancel, act_one] at hh
    exact hh.symm

def restriction (C : Submodule Bit (I → K)) : stabilizer C →* (C ≃ₗ[Bit] C) where
  toFun g :=
    { toFun := fun w => ⟨act g.val w.val, (g.prop _).mp w.prop⟩
      invFun := fun w => ⟨act g.val⁻¹ w.val, ((g⁻¹).prop _).mp w.prop⟩
      left_inv := by intro w; apply Subtype.ext; simp [← act_mul]
      right_inv := by intro w; apply Subtype.ext; simp [← act_mul]
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by apply LinearEquiv.ext; intro w; rfl
  map_mul' := by intros; apply LinearEquiv.ext; intro w; rfl

end Monomial
end Atlas.Codes
