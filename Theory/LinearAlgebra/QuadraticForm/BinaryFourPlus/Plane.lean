module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Prod

/-!
# The anisotropic binary plane and its three nonzero vectors

The form x² + xy + y² is one on each nonzero vector of the binary plane.
Number these vectors as (1,0), (0,1), (1,1). Extending a permutation by fixing
zero gives a linear automorphism; restriction to the nonzero vectors is its
inverse. Thus the comparison with S₃ retains the actual linear action.

This supplies the two plane factors in the concrete O₄⁺(2) model used in
Aschbacher–Smith, Lemma 14.2.21 (printed p.988). The finite checks below involve
only the four plane vectors and the six permutations of three points.
-/

public section

namespace BinaryFourPlus
abbrev Plane := Fin 2 → ZMod 2

@[expose] def planeQ : QuadraticForm (ZMod 2) Plane :=
  QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 + QuadraticMap.proj 1 1

@[expose] def nonzeroVector (i : Fin 3) : Plane := ![![1,0], ![0,1], ![1,1]] i

private def planeCoordinates : Option (Fin 3) ≃ Plane where
  toFun x := match x with | none => 0 | some i => nonzeroVector i
  invFun x := if x 0 = 0 then (if x 1 = 0 then none else some 1)
    else (if x 1 = 0 then some 0 else some 2)
  left_inv := by decide
  right_inv := by decide

private def planePermutation (p : Equiv.Perm (Fin 3)) : Plane ≃ Plane :=
  planeCoordinates.symm.trans ((Equiv.optionCongr p).trans planeCoordinates)

private theorem planePermutation_add : ∀ (p : Equiv.Perm (Fin 3)) (x y : Plane),
    planePermutation p (x+y) = planePermutation p x + planePermutation p y := by decide
private theorem planePermutation_smul : ∀ (p : Equiv.Perm (Fin 3)) (a : ZMod 2) (x : Plane),
    planePermutation p (a • x) = a • planePermutation p x := by decide

def planeLinear (p : Equiv.Perm (Fin 3)) : Plane ≃ₗ[ZMod 2] Plane where
  __ := planePermutation p
  map_add' := planePermutation_add p
  map_smul' := planePermutation_smul p

@[simp] theorem planeLinear_nonzeroVector (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    planeLinear p (nonzeroVector i) = nonzeroVector (p i) := by
  change planeCoordinates ((Equiv.optionCongr p)
    (planeCoordinates.symm (planeCoordinates (some i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem nonzeroVector_injective : Function.Injective nonzeroVector := by
  intro i j h
  exact Option.some.inj (planeCoordinates.injective h)

theorem planeLinear_injective : Function.Injective planeLinear := by
  intro p r h
  apply Equiv.ext
  intro i
  apply nonzeroVector_injective
  simpa only [planeLinear_nonzeroVector] using congrArg (fun a : Plane ≃ₗ[ZMod 2] Plane =>
    a (nonzeroVector i)) h

@[simp] theorem planeLinear_one : planeLinear 1 = 1 := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨o,rfl⟩ := planeCoordinates.surjective x
  cases o with
  | none => change planeLinear 1 0 = 0; exact map_zero _
  | some i => exact planeLinear_nonzeroVector 1 i

@[simp] theorem planeLinear_mul (p r : Equiv.Perm (Fin 3)) :
    planeLinear (p*r) = planeLinear p * planeLinear r := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨o,rfl⟩ := planeCoordinates.surjective x
  cases o with
  | none => change planeLinear (p*r) 0 = planeLinear p (planeLinear r 0); simp
  | some i => change planeLinear (p*r) (nonzeroVector i) = planeLinear p (planeLinear r (nonzeroVector i))
              simp only [planeLinear_nonzeroVector, Equiv.Perm.mul_apply]

theorem planeLinear_preserves : ∀ (p : Equiv.Perm (Fin 3)) (x : Plane),
    planeQ (planeLinear p x) = planeQ x := by decide

def nonzeroCoordinates : Fin 3 ≃ {v : Plane // v ≠ 0} where
  toFun i := ⟨nonzeroVector i, (by decide : ∀i, nonzeroVector i ≠ 0) i⟩
  invFun x := if x.1 0 = 0 then 1 else if x.1 1 = 0 then 0 else 2
  left_inv := by decide
  right_inv := by decide

def planeAutPerm (a : Plane ≃ₗ[ZMod 2] Plane) : Equiv.Perm (Fin 3) :=
  nonzeroCoordinates.trans ((a.toEquiv.subtypeEquiv (by
    intro x
    exact (not_congr a.map_eq_zero_iff).symm)).trans nonzeroCoordinates.symm)

theorem planeAutPerm_apply (a : Plane ≃ₗ[ZMod 2] Plane) (i : Fin 3) :
    nonzeroVector (planeAutPerm a i) = a (nonzeroVector i) := by
  change (nonzeroCoordinates (nonzeroCoordinates.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem planeLinear_planeAutPerm (a : Plane ≃ₗ[ZMod 2] Plane) :
    planeLinear (planeAutPerm a) = a := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨o,rfl⟩ := planeCoordinates.surjective x
  cases o with
  | none => change planeLinear (planeAutPerm a) 0 = a 0; simp
  | some i => exact (planeLinear_nonzeroVector _ i).trans (planeAutPerm_apply a i)

/-- A binary plane automorphism is exactly a permutation of its three nonzero vectors. -/
@[expose] def planeAutEquiv : (Plane ≃ₗ[ZMod 2] Plane) ≃* Equiv.Perm (Fin 3) where
  toFun := planeAutPerm
  invFun := planeLinear
  left_inv := planeLinear_planeAutPerm
  right_inv p := planeLinear_injective (planeLinear_planeAutPerm (planeLinear p))
  map_mul' a b := planeLinear_injective (by
    rw [planeLinear_planeAutPerm, planeLinear_mul, planeLinear_planeAutPerm,
      planeLinear_planeAutPerm])

@[simp] theorem planeAutEquiv_symm_apply (p : Equiv.Perm (Fin 3)) :
    planeAutEquiv.symm p = planeLinear p := rfl

theorem plane_aut_preserves (a : Plane ≃ₗ[ZMod 2] Plane) (v : Plane) :
    planeQ (a v) = planeQ v := by
  rw [← planeLinear_planeAutPerm a]
  exact planeLinear_preserves _ v

end BinaryFourPlus
