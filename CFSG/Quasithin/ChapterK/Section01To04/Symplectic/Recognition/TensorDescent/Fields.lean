module

public import Theory.Representation.FirstCohomologyCyclic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The quadratic defining-field extension in K.3.4

Finite-field embeddings realize the actual Schur field of order 2^s inside
its defining field of order 2^(2s). Relative Frobenius is the nonidentity
involution and acts by the 2^s power. This field calculation supplies the
quadratic extension used by the tensor descent, without replacing either
field by an isomorphic carrier.

Source: Aschbacher--Smith K.3.4, printed p.456; GLS3, Remark 2.8.8.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
noncomputable section
variable {E F : Type*} [Field E] [Field F] [Finite E] [Finite F]
  [Algebra (ZMod 2) E] [Algebra (ZMod 2) F]

/-- Realize the specified fields as a quadratic extension with its explicit Frobenius. -/
theorem exists_quadratic_extension {s : ℕ} (hs : 0 < s)
    (hE : Nat.card E = 2^s) (hF : Nat.card F = 2^(2*s)) :
    ∃ a : Algebra E F, letI := a
      ∃ σ : F ≃ₐ[E] F, σ ≠ AlgEquiv.refl ∧ Function.Involutive σ ∧
        Module.finrank E F = 2 ∧ ∀ x, σ x = x ^ (2^s) := by
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  obtain ⟨i⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := E) (L := F) (by
      rw [OneCohomology.coefficient_finrank_of_card 2 s hE,
        OneCohomology.coefficient_finrank_of_card 2 (2*s) hF]
      exact dvd_mul_left _ _)
  let a : Algebra E F := i.toRingHom.toAlgebra
  let := a
  let : Module.Finite E F := Module.Finite.of_finite
  have hd : Module.finrank E F = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := E) (V := F)
    rw [hE, hF, ← pow_mul] at hc
    have he := Nat.pow_right_injective (by decide : 1 < 2) hc
    nlinarith
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic E F
  have ho : orderOf σ = 2 := (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic E F).trans hd
  refine ⟨a, σ, ?_, ?_, hd, ?_⟩
  · intro h
    have : σ = 1 := h
    simp [this] at ho
  · intro x
    have hpow : σ^2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one σ
    exact congrArg (fun f : F ≃ₐ[E] F => f x) hpow
  · intro x
    change x ^ Fintype.card E = x ^ (2^s)
    rw [← Nat.card_eq_fintype_card, hE]
end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
