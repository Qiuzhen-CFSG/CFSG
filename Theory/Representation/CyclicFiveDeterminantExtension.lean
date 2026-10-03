module

public import Theory.Representation.CyclicInvariantExtension
public import Theory.Character.LinearTwist
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant normalization for cyclic-five quartic extensions

An invariant irreducible quartic representation extends across an action of a
cyclic group of order five. Twist an extension by its complement determinant,
inflated along the projection. The new complement determinant is the fifth
power of the old one, hence one; the restriction to the base group is unchanged.

This is the normalization step for the rational extension in Lyons,
*A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

noncomputable section
namespace Representation
variable {K : Type*} [Group K] [Finite K]

/-- Twisting by the complement determinant normalizes a quartic extension. -/
theorem exists_cyclicFive_det_one_extension
    (α : Multiplicative (ZMod 5) →* MulAut K)
    (ρ : Representation ℂ K (Fin 4 → ℂ)) [IsIrreducible ρ]
    (hinv : ∀ t s, ρ.character (α t s) = ρ.character s) :
    ∃ σ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ),
      IsIrreducible σ ∧ σ.comp SemidirectProduct.inl = ρ ∧
      ∀ t, LinearMap.det (σ (SemidirectProduct.inr t)) = 1 := by
  obtain ⟨τ, _, hτ⟩ := exists_cyclic_semidirect_extension α ρ hinv
  let δ : Multiplicative (ZMod 5) →* ℂ :=
    LinearMap.det.comp (τ.comp SemidirectProduct.inr)
  let χ : (K ⋊[α] Multiplicative (ZMod 5)) →* ℂ :=
    δ.comp SemidirectProduct.rightHom
  let σ := τ.linearTwist χ
  have hres : σ.comp SemidirectProduct.inl = ρ := by
    rw [← hτ]
    apply MonoidHom.ext
    intro k
    change χ (SemidirectProduct.inl k) • τ (SemidirectProduct.inl k) = _
    simp [χ]
  let : IsIrreducible (σ.comp SemidirectProduct.inl) := hres.symm ▸ inferInstance
  refine ⟨σ, isIrreducible_of_comp σ SemidirectProduct.inl, hres, ?_⟩
  intro t
  have ht : t ^ 5 = 1 := by simpa using (pow_card_eq_one (x := t))
  have hδ : (δ t) ^ 5 = 1 := by rw [← map_pow, ht, map_one]
  change LinearMap.det (χ (SemidirectProduct.inr t) • τ (SemidirectProduct.inr t)) = 1
  rw [LinearMap.det_smul]
  simpa [χ, δ, Module.finrank_pi, ← pow_succ] using hδ
end Representation
