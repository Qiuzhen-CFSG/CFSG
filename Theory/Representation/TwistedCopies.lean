module
public import Theory.Representation.SchurCopies
public import Theory.Representation.InnerUntwist
/-!
# TwistedCopies

An actor inducing a marked inner action on copies of an absolutely irreducible module has literal twisted regular coordinates. The multiplicity representation is constructed by Schur scalar blocks after removing the inner factor. The original actor is retained. Source application: Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
open Module Representation
namespace Representation.SchurCopies
variable {k D A E I P : Type*} [Field k] [Group D] [Group A] [Group P]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]

private def copies (σ : Representation k D E) : Representation k D (I → E) where
  toFun d := LinearMap.pi (fun i => (σ d).comp (LinearMap.proj i))
  map_one' := by ext x i; simp
  map_mul' d f := by ext x i; simp [Module.End.mul_apply]

/-- An inner actor on irreducible copies has literal twisted regular fibers. -/
theorem exists_twisted_fiber_action
    (σ : Representation k D E) [IsIrreducible σ] [IsAbsolutelyIrreducible σ]
    (τ : Representation k A (I → E)) (φ : A →* P) (j : P →* D)
    (hc : ∀ a d x, τ a (fun i => σ d (x i)) =
      fun i => σ (j (φ a) * d * (j (φ a))⁻¹) (τ a x i))
    (e : E ≃ₗ[k] (P → k))
    (he : ∀ p v x, e (σ (j p) v) x = e v (p⁻¹*x)) :
    ∃ μ : Representation k A (I → k),
      ∀ a f x, (fun i => e (τ a f i) x) =
        μ a (fun i => e (f i) ((φ a)⁻¹*x)) := by
  let ρ := copies (I := I) σ
  have hcov (a : A) (d : D) :
      τ a * ρ d = ρ ((j.comp φ) a * d * ((j.comp φ) a)⁻¹) * τ a := by
    apply LinearMap.ext
    intro x
    exact hc a d x
  let u := innerUntwist ρ τ (j.comp φ) hcov
  obtain ⟨μ,hμ⟩ := exists_fiber_action σ u (fun a d x =>
    LinearMap.congr_fun (innerUntwist_commute ρ τ (j.comp φ) hcov a d) x) e
  refine ⟨μ, ?_⟩
  intro a f x
  have ht := innerUntwist_reconstruct ρ τ (j.comp φ) hcov a
  rw [ht]
  change (fun i => e (σ (j (φ a)) (u a f i)) x) = _
  simp only [he]
  exact hμ a f ((φ a)⁻¹*x)
end Representation.SchurCopies
