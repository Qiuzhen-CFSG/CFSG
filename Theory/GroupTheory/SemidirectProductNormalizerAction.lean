module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Full normalizer action in a semidirect product

If the action defining `N ⋊ K` maps `K` onto `Aut(N)`, its canonical normal
subgroup realizes every automorphism by conjugation by the complement.
-/

namespace SemidirectProduct

/-- The canonical normal factor has full normalizer action when the defining
action is surjective. -/
public theorem normalizerMonoidHom_inl_surjective
    {N K : Type*} [Group N] [Group K] (φ : K →* MulAut N)
    (hφ : Function.Surjective φ) :
    Function.Surjective (inl : N →* SemidirectProduct N K φ).range.normalizerMonoidHom := by
  let B := (inl : N →* SemidirectProduct N K φ).range
  let e : N ≃* B := MonoidHom.ofInjective inl_injective
  intro α
  obtain ⟨k, hk⟩ := hφ (e.trans (α.trans e.symm))
  have hB : B.Normal := by
    dsimp [B]
    rw [range_inl_eq_ker_rightHom]
    infer_instance
  have hn : inr k ∈ Subgroup.normalizer (B : Set (SemidirectProduct N K φ)) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  refine ⟨⟨inr k, hn⟩, ?_⟩
  apply MulEquiv.ext
  intro b
  obtain ⟨n, rfl⟩ := e.surjective b
  apply Subtype.ext
  change inr k * inl n * (inr k)⁻¹ = (α (e n) : SemidirectProduct N K φ)
  rw [← map_inv, ← inl_aut, hk]
  exact congrArg (fun b : B => (b : SemidirectProduct N K φ)) (e.apply_symm_apply (α (e n)))

end SemidirectProduct
