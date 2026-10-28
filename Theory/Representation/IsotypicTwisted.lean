module
public import Theory.Representation.IsotypicStable
public import Theory.Representation.TwistedCopies
/-!
# Actual twisted coordinates on an isotypic component

The canonical simple isotypic part is invariant under an actor inducing
specified inner automorphisms. Its finite copy coordinates and the Schur
multiplicity construction give a genuine equivariant function-space model.
The original actor is retained, including its entire kernel.

Source application: the Suzuki Steinberg isotypic part in the terminal
quasithin argument, Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
open scoped MonoidAlgebra
open Module Representation
namespace Representation.SchurCopies
variable {k D A V E P : Type*} [Field k] [Group D] [Group A] [Group P]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  [Fintype P] [DecidableEq P]

/-- Construct the full twisted action on the canonical isotypic part. -/
theorem isotypic_twisted_coordinates
    (ρ : Representation k D V) (σ : Representation k D E)
    [IsIrreducible σ] [IsAbsolutelyIrreducible σ]
    (τ : Representation k A V) (φ : A →* P) (j : P →* D)
    (hc : ∀ a d, τ a * ρ d = ρ (j (φ a) * d * (j (φ a))⁻¹) * τ a)
    (eR : E ≃ₗ[k] (P → k))
    (heR : ∀ p v x, eR (σ (j p) v) x = eR v (p⁻¹*x)) :
    let S := Subrepresentation.ofSubmodule' (isotypicComponent k[D] ρ.asModule σ.asModule)
    ∃ (n : ℕ) (τS : Representation k A S.toSubmodule)
      (c : S.toSubmodule ≃ₗ[k] (P → Fin n → k)) (μ : Representation k A (Fin n → k)),
      (∀ a v, (τS a v : V) = τ a v) ∧
      ∀ a v x, c (τS a v) x = μ a (c v ((φ a)⁻¹*x)) := by
  classical
  let S := Subrepresentation.ofSubmodule' (isotypicComponent k[D] ρ.asModule σ.asModule)
  have hs (a : A) : ∀ v ∈ S.toSubmodule, τ a v ∈ S.toSubmodule :=
    fun v hv => isotypic_stable_of_inner ρ σ τ (j.comp φ) hc a v hv
  let τS : Representation k A S.toSubmodule := {
    toFun a := (τ a).restrict (fun v hv => hs a v hv)
    map_one' := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (τ.map_one) v
    map_mul' a b := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (τ.map_mul a b) v }
  obtain ⟨n,e,he⟩ := isotypic_finite_rep_coordinates ρ σ
  let τc : Representation k A (Fin n → E) := e.conjRingEquiv.toMonoidHom.comp τS
  have hτc (a : A) (v : S.toSubmodule) : τc a (e v) = e (τS a v) := by
    change e (τS a (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have hcov (a : A) (d : D) (x : Fin n → E) :
      τc a (fun i => σ d (x i)) =
        fun i => σ (j (φ a) * d * (j (φ a))⁻¹) (τc a x i) := by
    obtain ⟨v,rfl⟩ := e.surjective x
    rw [← he d v,hτc,hτc,← he]
    apply congrArg e
    apply Subtype.ext
    exact LinearMap.congr_fun (hc a d) v
  obtain ⟨μ,hμ⟩ := exists_twisted_fiber_action σ τc φ j hcov eR heR
  let c₁ : (Fin n → E) ≃ₗ[k] (Fin n → P → k) := LinearEquiv.piCongrRight fun _ => eR
  let c₂ : (Fin n → P → k) ≃ₗ[k] (P → Fin n → k) := {
    toFun f x i := f i x
    invFun f i x := f x i
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  refine ⟨n,τS,e.trans (c₁.trans c₂),μ,fun _ _ => rfl,?_⟩
  intro a v x
  have h := hμ a (e v) x
  rw [hτc] at h
  exact h
end Representation.SchurCopies
