module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic

/-!
# Natural tensor models and scalar-twist bounds

The carriers are the actual column representation of SL₂(F) and its tensor
square over F, restricted to the binary prime field. A moved scalar gives
half-dimension displacement bounds even when an operator mixes natural summands.
The coordinate flip supplies the elementary off-diagonal tensor calculation.

Source: GLS, vol. 2, Theorem 26.24, final paragraph, ChapterG.tex, lines 1240–1248.
These are local model lemmas; existence of an invariant natural section is a
separate representation-theoretic assertion.
-/

@[expose] public section

open Module
open scoped TensorProduct

namespace Representation.BinaryOffender.NaturalTensor

variable (F : Type*) [Field F]

abbrev NaturalSpace := Fin 2 → F
abbrev TensorSpace := NaturalSpace F ⊗[F] NaturalSpace F

def tensorAction : Representation F
    (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (TensorSpace F) where
  toFun g := TensorProduct.map (specialLinearNatural 2 g.1) (specialLinearNatural 2 g.2)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_eq_comp, TensorProduct.map_comp]

def tensorCoordinates : TensorSpace F ≃ₗ[F] (Fin 2 → Fin 2 → F) :=
  TensorProduct.piScalarRight F F (NaturalSpace F) (Fin 2)

theorem tensorCoordinates_tmul (x y : NaturalSpace F) (i j : Fin 2) :
    tensorCoordinates F (x ⊗ₜ[F] y) i j = y i * x j := by
  simp [tensorCoordinates]

def tensorFlip : Module.End F (TensorSpace F) :=
  (_root_.TensorProduct.comm F (NaturalSpace F) (NaturalSpace F)).toLinearMap

theorem tensorFlip_tmul (x y : NaturalSpace F) : tensorFlip F (x ⊗ₜ[F] y) = y ⊗ₜ[F] x :=
  rfl

theorem tensorFlip_intertwines
    (g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (z : TensorSpace F) :
    tensorFlip F (tensorAction F g z) = tensorAction F (g.2, g.1) (tensorFlip F z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp [hx, hy]

variable [Algebra (ZMod 2) F]

def binaryTensorAction : Representation (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (TensorSpace F) where
  toFun g := (tensorAction F g).restrictScalars (ZMod 2)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

variable [Finite F]

theorem finrank_field {n : ℕ} (hF : Nat.card F = 2 ^ n) : finrank (ZMod 2) F = n := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_zmod, hF] at hc
  exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm

theorem finrank_natural {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    finrank (ZMod 2) (NaturalSpace F) = 2 * n := by
  simp [NaturalSpace, Module.finrank_pi_fintype, finrank_field F hF]

theorem finrank_tensor {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    finrank (ZMod 2) (TensorSpace F) = 4 * n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (TensorSpace F), finrank_field F hF]
  simp [TensorSpace, NaturalSpace]
  omega

theorem field_tensor_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (T : Module.End (ZMod 2) (TensorSpace F)) (σ : F →+* F)
    (hσ : ∃ a, σ a ≠ a) (hT : ∀ a v, T (a • v) = σ a • T v) :
    2 * n ≤ operatorFixedCodim T := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  have h := finrank_le_twice_operatorFixedCodim T σ hσ hT
  rw [finrank_tensor F hF] at h
  omega

theorem field_natural_sum_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → NaturalSpace F)) (σ : F →+* F)
    (hσ : ∃ a, σ a ≠ a) (hT : ∀ a v, T (a • v) = σ a • T v) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  have h := finrank_le_twice_operatorFixedCodim T σ hσ hT
  simp only [Module.finrank_pi_fintype, finrank_natural F hF, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h
  nlinarith

theorem flip_tensor_bound {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    n ≤ operatorFixedCodim ((tensorFlip F).restrictScalars (ZMod 2)) := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  let e₀ : NaturalSpace F := Pi.single 0 1
  let e₁ : NaturalSpace F := Pi.single 1 1
  let j : F →ₗ[F] TensorSpace F :=
    (TensorProduct.mk F (NaturalSpace F) (NaturalSpace F) e₀).comp
      (LinearMap.toSpanSingleton F (NaturalSpace F) e₁)
  let T := (tensorFlip F).restrictScalars (ZMod 2)
  let f : F →ₗ[ZMod 2] LinearMap.range (T - 1) :=
    ((T - 1).comp (j.restrictScalars (ZMod 2))).codRestrict _ (fun a => ⟨j a, rfl⟩)
  have hf (a : F) : tensorCoordinates F (f a) 0 1 = a := by
    change tensorCoordinates F ((tensorFlip F) (e₀ ⊗ₜ[F] (a • e₁)) -
      (e₀ ⊗ₜ[F] (a • e₁))) 0 1 = a
    rw [tensorFlip_tmul, map_sub]
    simp [tensorCoordinates_tmul, e₀, e₁]
  have hi : Function.Injective f := by
    intro a b h
    simpa only [hf] using congrArg (fun z => tensorCoordinates F z.val 0 1) h
  rw [← finrank_field F hF]
  exact LinearMap.finrank_le_finrank_of_injective hi

end Representation.BinaryOffender.NaturalTensor
