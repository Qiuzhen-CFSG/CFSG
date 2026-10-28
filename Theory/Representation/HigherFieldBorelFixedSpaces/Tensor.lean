module

public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Fixed spaces on binary duals and external tensors

A fixed-point-free operator on a finite binary space has invertible difference
from the identity, and hence has zero fixed space on the binary dual.
Coordinate projections identify the B-fixed vectors on U tensor N, when B
acts trivially on N, with copies of the B-fixed vectors on U. The external
tensor representation retains both actors, including the concrete permutation
S₃ acting on its natural even-weight binary plane.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 13.8.20, printed pp.954–955 (PDF pp.971–972).
-/

@[expose] public section
open scoped TensorProduct
namespace Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
variable {K U : Type*} [Group K] [AddCommGroup U]

/-- A fixed-point-free operator on a finite module has no nonzero dual fixed vector. -/
theorem dual_fixed_eq_zero {k : Type*} [CommRing k] [Module k U] [Finite U] (ρ : Representation k K U)
    (g : K) (hg : ∀ u : U, ρ g u = u → u = 0)
    (f : Module.Dual k U) (hf : ρ.dual g f = f) : f = 0 := by
  have hinj : Function.Injective (ρ g - (LinearMap.id : U →ₗ[k] U) : U →ₗ[k] U) := by
    apply (LinearMap.ker_eq_bot (f := ρ g - (LinearMap.id : U →ₗ[k] U))).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    exact hg u (sub_eq_zero.mp hu)
  have hsurj := Finite.surjective_of_injective hinj
  apply LinearMap.ext
  intro u
  obtain ⟨v, rfl⟩ := hsurj u
  have h := congrArg (fun t : Module.Dual k U => t (ρ g v)) hf
  change f (ρ g⁻¹ (ρ g v)) = f (ρ g v) at h
  have hcancel : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hcancel] at h
  change f (ρ g v - v) = 0
  rw [map_sub, ← h, sub_self]

variable [Module (ZMod 2) U]

/-- Coordinate projections of a genuine tensor with a trivial second factor. -/
theorem tensor_pi_fixed_eq_zero {ι : Type*} [Fintype ι] (ρ : Representation (ZMod 2) K U) (B : Subgroup K)
    (hfixed : fixedSpace ρ B = ⊥)
    (z : U ⊗[ZMod 2] (ι → ZMod 2))
    (hz : ∀ b : B, TensorProduct.map (ρ b) LinearMap.id z = z) : z = 0 := by
  classical
  let e := TensorProduct.piScalarRight (ZMod 2) (ZMod 2) U ι
  have hcoord (g : K) (z : U ⊗[ZMod 2] (ι → ZMod 2)) (i : ι) :
      e (TensorProduct.map (ρ g) LinearMap.id z) i = ρ g (e z i) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have he : e z = 0 := by
    ext i
    have hm : e z i ∈ fixedSpace ρ B := by
      intro b
      change ρ b (e z i) = e z i
      rw [← hcoord, hz b]
    rwa [hfixed, Submodule.mem_bot] at hm
  exact e.injective (he.trans e.map_zero.symm)

theorem tensor_fixed_eq_zero {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N]
    (ρ : Representation (ZMod 2) K U) (B : Subgroup K)
    (hfixed : fixedSpace ρ B = ⊥) (z : U ⊗[ZMod 2] N)
    (hz : ∀ b : B, TensorProduct.map (ρ b) LinearMap.id z = z) : z = 0 := by
  let e := TensorProduct.congr (LinearEquiv.refl (ZMod 2) U)
    (Module.finBasis (ZMod 2) N).equivFun
  have he (g : K) (x : U ⊗[ZMod 2] N) :
      e (TensorProduct.map (ρ g) LinearMap.id x) =
        TensorProduct.map (ρ g) LinearMap.id (e x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [e]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply e.injective
  rw [map_zero]
  apply tensor_pi_fixed_eq_zero ρ B hfixed
  intro b
  rw [← he, hz b]

/-- The actual external tensor representation, retaining both actors. -/
noncomputable def externalTensor {L N : Type*} [Group L] [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) K U)
    (σ : Representation (ZMod 2) L N) :
    Representation (ZMod 2) (K × L) (U ⊗[ZMod 2] N) :=
  Representation.tprod (ρ.comp (MonoidHom.fst K L)) (σ.comp (MonoidHom.snd K L))

/-- Vanishing on the first factor passes to an external tensor product. -/
theorem externalTensor_fixedSpace {L N : Type*} [Group L] [AddCommGroup N]
    [Module (ZMod 2) N] [FiniteDimensional (ZMod 2) N]
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L N)
    (B : Subgroup K) (hfixed : fixedSpace ρ B = ⊥) :
    fixedSpace (externalTensor ρ σ) (B.prod ⊥) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply tensor_fixed_eq_zero ρ B hfixed z
  intro b
  have h := hz ⟨(b, 1), b.property, (⊥ : Subgroup L).one_mem⟩
  change TensorProduct.map (ρ b) (σ 1) z = z at h
  simpa only [map_one, Module.End.one_eq_id] using h

/-- The second actor is the actual permutation group S₃ on its binary natural
augmentation module, with no family tag or dimension-only comparison. -/
theorem naturalS3_tensor_fixedSpace
    (ρ : Representation (ZMod 2) K U) (B : Subgroup K)
    (hfixed : fixedSpace ρ B = ⊥) :
    fixedSpace (externalTensor ρ (BinaryPermutation.coreRepresentation (Fin 3)))
      (B.prod ⊥) = ⊥ :=
  externalTensor_fixedSpace ρ _ B hfixed

/-- Restriction to the first actor gives the fixed-space calculation in the
form needed by the odd-index extension theorem for K. -/
theorem externalTensor_left_fixedSpace {L N : Type*} [Group L] [AddCommGroup N]
    [Module (ZMod 2) N] [FiniteDimensional (ZMod 2) N]
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L N)
    (B : Subgroup K) (hfixed : fixedSpace ρ B = ⊥) :
    fixedSpace ((externalTensor ρ σ).comp (MonoidHom.inl K L)) B = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply tensor_fixed_eq_zero ρ B hfixed z
  intro b
  have h := hz b
  change TensorProduct.map (ρ b) (σ 1) z = z at h
  simpa only [map_one, Module.End.one_eq_id] using h
end Representation.HigherFieldBorelFixedSpaces


