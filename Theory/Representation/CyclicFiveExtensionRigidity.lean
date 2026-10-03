module

public import Theory.Representation.CharacterEquivalence
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Data.ZMod.Basic


/-!
# Uniqueness of normalized cyclic-five quartic extensions

Two complex quartic representations of a semidirect product by a cyclic group
of order five have the same character if their restrictions have the same
irreducible character and their complement operators all have determinant one.

First identify the restrictions by a representation equivalence. Schur's lemma
then makes the quotient of corresponding complement operators scalar. Its fourth
power is one by the determinant condition, and its fifth power is one by the
order of the complement. The scalar is therefore one, so the equivalence of
restrictions intertwines the full representations.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

open Representation
noncomputable section
namespace Representation
variable {K : Type*} [Group K] [Finite K]
  (α : Multiplicative (ZMod 5) →* MulAut K)
  (σ τ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ))

omit [Finite K] in
private theorem eq_of_restriction_eq
    [IsIrreducible (σ.comp SemidirectProduct.inl)]
    (hres : ∀ k, τ (SemidirectProduct.inl k) = σ (SemidirectProduct.inl k))
    (hσ : ∀ t, LinearMap.det (σ (SemidirectProduct.inr t)) = 1)
    (hτ : ∀ t, LinearMap.det (τ (SemidirectProduct.inr t)) = 1) : τ = σ := by
  have hright : ∀ t, τ (SemidirectProduct.inr t) = σ (SemidirectProduct.inr t) := by
    intro t
    let a : K ⋊[α] Multiplicative (ZMod 5) := SemidirectProduct.inr t
    have hconj (k : K) : a * SemidirectProduct.inl k * a⁻¹ =
        SemidirectProduct.inl (α t k) := by
      simpa [a] using (SemidirectProduct.inl_aut (φ := α) t k).symm
    have hcomm (k : K) :
        (σ a⁻¹ * τ a) * σ (SemidirectProduct.inl k) =
          σ (SemidirectProduct.inl k) * (σ a⁻¹ * τ a) := by
      calc
        _ = σ a⁻¹ * τ (a * SemidirectProduct.inl k) := by rw [map_mul, hres, mul_assoc]
        _ = σ a⁻¹ * τ (SemidirectProduct.inl (α t k) * a) := by
          rw [← hconj, inv_mul_cancel_right]
        _ = σ (a⁻¹ * SemidirectProduct.inl (α t k)) * τ a := by
          rw [map_mul, hres, map_mul, mul_assoc]
        _ = σ (SemidirectProduct.inl k * a⁻¹) * τ a := by
          rw [← hconj]; simp only [← mul_assoc, inv_mul_cancel, one_mul]
        _ = _ := by rw [map_mul, mul_assoc]
    let D : Representation.IntertwiningMap (σ.comp SemidirectProduct.inl)
        (σ.comp SemidirectProduct.inl) := ⟨σ a⁻¹ * τ a, hcomm⟩
    obtain ⟨c, hc⟩ :=
      (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := σ.comp SemidirectProduct.inl)).surjective D
    have hD : σ a⁻¹ * τ a = c • (1 : Module.End ℂ (Fin 4 → ℂ)) := by
      exact (congrArg IntertwiningMap.toLinearMap hc).symm
    have heq : τ a = c • σ a := by
      have := congrArg (fun f => σ a * f) hD
      simpa only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul,
        mul_smul_comm, mul_one] using this
    have hc4 : c ^ 4 = 1 := by
      have hd := congrArg LinearMap.det heq
      rw [LinearMap.det_smul] at hd
      simpa [a, hσ, hτ, Module.finrank_pi] using hd.symm
    have ha : a ^ 5 = 1 := by
      dsimp [a]
      rw [← map_pow]
      have ht : t ^ 5 = 1 := by simpa using (pow_card_eq_one (x := t))
      rw [ht, map_one]
    have hc5 : c ^ 5 = 1 := by
      have hp := congrArg (fun f : Module.End ℂ (Fin 4 → ℂ) => f ^ 5) heq
      rw [smul_pow, ← map_pow τ, ← map_pow σ, ha, map_one, map_one] at hp
      have hv := congrArg (fun f : Module.End ℂ (Fin 4 → ℂ) => f (fun _ => 1) 0) hp
      simpa using hv.symm
    have hc1 : c = 1 := by simpa [pow_succ, hc4] using hc5
    simpa [hc1] using heq
  apply MonoidHom.ext
  intro g
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul, map_mul, hres, hright]

/-- Determinant-one quartic extensions through an order-five action have the same
character whenever their irreducible restrictions have the same character. -/
theorem cyclicFive_det_one_extension_character_unique
    [IsIrreducible (σ.comp SemidirectProduct.inl)]
    (hchar : Representation.character (τ.comp SemidirectProduct.inl) =
      Representation.character (σ.comp SemidirectProduct.inl))
    (hσ : ∀ t, LinearMap.det (σ (SemidirectProduct.inr t)) = 1)
    (hτ : ∀ t, LinearMap.det (τ (SemidirectProduct.inr t)) = 1) :
    τ.character = σ.character := by
  obtain ⟨e⟩ := equiv_of_character_eq
    (τ.comp SemidirectProduct.inl) (σ.comp SemidirectProduct.inl) hchar
  let τ' : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ) :=
    (e.toLinearEquiv.conjAlgEquiv ℂ).toMonoidHom.comp τ
  have hres : ∀ k, τ' (SemidirectProduct.inl k) = σ (SemidirectProduct.inl k) := by
    intro k
    exact e.conj_apply_self k
  have hdet : ∀ t, LinearMap.det (τ' (SemidirectProduct.inr t)) = 1 := by
    intro t
    change LinearMap.det (e.toLinearEquiv.toLinearMap ∘ₗ
      τ (SemidirectProduct.inr t) ∘ₗ e.toLinearEquiv.symm.toLinearMap) = 1
    rw [LinearMap.det_conj, hτ]
  have heq : τ' = σ := eq_of_restriction_eq α σ τ' hres hσ hdet
  have E : τ.Equiv τ' := Representation.Equiv.mk e.toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    change e.toLinearEquiv (τ g v) =
      e.toLinearEquiv (τ g (e.toLinearEquiv.symm (e.toLinearEquiv v)))
    rw [LinearEquiv.symm_apply_apply])
  rw [← heq]
  exact char_iso E

end Representation
