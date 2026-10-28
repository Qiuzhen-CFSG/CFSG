module

public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The singular-vector obstruction in the A₅ tensor module

The displacement of a transposition on the five-point augmentation core is
zero or a weight-two, hence nonsingular, vector. Contracting the second
tensor factor proves that a tensor u ⊗ w with nonzero singular u and nonzero
w cannot lie in its displacement space. The coordinate certificate checks
only two positions and the 32 binary words, never the tensor actor group.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.6(a), printed p.1008. The source vector u₁+u₂ is u ⊗ (w₁+w₂)
in the two copies of the A₅ core.
-/

public section
open TensorProduct
namespace BinaryPermutation.FiveTensorSingular
open FiveGeometry FiveTensorQuadratic

private theorem transposition_displacement_singular (i j : Fin 5) (x : core (Fin 5))
    (h : form (coreRepresentation (Fin 5) (Equiv.swap i j) x - x) = 0) :
    coreRepresentation (Fin 5) (Equiv.swap i j) x - x = 0 := by
  have cert : ∀ (i j : Fin 5) (x : Full (Fin 5)),
      let y := representation (Fin 5) (Equiv.swap i j) x - x
      (∑ a : Fin 5, ∑ b : Fin 5 with a < b, y a * y b) = 0 → y = 0 := by decide
  exact Subtype.ext (cert i j x.val h)

/-- Nonzero singular core vectors lie outside every transposition displacement. -/
theorem singular_not_mem_displacement (i j : Fin 5) (u : core (Fin 5)) (hu : u ≠ 0) (hs : form u = 0) :
    u ∉ LinearMap.range (coreRepresentation (Fin 5) (Equiv.swap i j) - LinearMap.id) := by
  rintro ⟨x, hx⟩
  change coreRepresentation (Fin 5) (Equiv.swap i j) x - x = u at hx
  exact hu (hx.symm.trans (transposition_displacement_singular i j x (hx ▸ hs)))

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
private def contract (φ : W →ₗ[ZMod 2] ZMod 2) :
    core (Fin 5) ⊗[ZMod 2] W →ₗ[ZMod 2] core (Fin 5) :=
  (TensorProduct.rid (ZMod 2) (core (Fin 5))).toLinearMap.comp
    (TensorProduct.map LinearMap.id φ)

private theorem contract_tmul (φ : W →ₗ[ZMod 2] ZMod 2) (v : core (Fin 5)) (w : W) :
    contract φ (v ⊗ₜ[ZMod 2] w) = φ w • v := by
  simp [contract]

private theorem contract_action (σ : Representation (ZMod 2) D W)
    (φ : W →ₗ[ZMod 2] ZMod 2) (g : Equiv.Perm (Fin 5))
    (z : core (Fin 5) ⊗[ZMod 2] W) :
    contract φ (tensorAction σ (g, 1) z) =
      coreRepresentation (Fin 5) g (contract φ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    change contract φ (TensorProduct.map (coreRepresentation (Fin 5) g) (σ 1)
      (v ⊗ₜ[ZMod 2] w)) = _
    rw [TensorProduct.map_tmul, map_one, Module.End.one_apply,
      contract_tmul, contract_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The singular exclusion persists in the external tensor product. -/
theorem singular_tensor_not_mem_displacement (σ : Representation (ZMod 2) D W) (i j : Fin 5)
    (u : core (Fin 5)) (hu : u ≠ 0) (hs : form u = 0)
    (w : W) (hw : w ≠ 0) :
    u ⊗ₜ[ZMod 2] w ∉ LinearMap.range (tensorAction σ (Equiv.swap i j, 1) - LinearMap.id) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hw
  rintro ⟨x, hx⟩
  change tensorAction σ (Equiv.swap i j, 1) x - x = u ⊗ₜ[ZMod 2] w at hx
  have hh := congrArg (contract φ) hx
  rw [map_sub, contract_action, contract_tmul, hφ, one_smul] at hh
  exact hu (hh.symm.trans (transposition_displacement_singular i j (contract φ x) (hh ▸ hs)))
end BinaryPermutation.FiveTensorSingular
