module
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.InnerUntwist
/-!
# IsotypicStable

Canonical isotypic components are stable under commuting operators and actors inducing the specified inner automorphisms. The proof uses full invariance of the group-algebra isotypic component and the actual inner-untwist representation. Source application: Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
open scoped MonoidAlgebra
open Module Representation
namespace Representation.SchurCopies
variable {k D V E : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup E] [Module k E]

/-- A component-commuting operator preserves its canonical isotypic part. -/
theorem isotypic_stable_of_commute
    (ρ : Representation k D V) (σ : Representation k D E) [IsIrreducible σ]
    (T : Module.End k V) (hc : ∀ d, T * ρ d = ρ d * T)
    (v : V) (hv : v ∈ (Subrepresentation.ofSubmodule'
      (isotypicComponent k[D] ρ.asModule σ.asModule)).toSubmodule) :
    T v ∈ (Subrepresentation.ofSubmodule'
      (isotypicComponent k[D] ρ.asModule σ.asModule)).toSubmodule := by
  let f : ρ.IntertwiningMap ρ := ⟨T,hc⟩
  let l := IntertwiningMap.equivLinearMapAsModule ρ ρ f
  exact (LinearMap.le_comap_isotypicComponent (R := k[D]) (M := ρ.asModule)
    (N := ρ.asModule) (S := σ.asModule) (f := l)) hv

/-- An actor inducing the marked inner automorphisms preserves the component. -/
theorem isotypic_stable_of_inner
    {A : Type*} [Group A]
    (ρ : Representation k D V) (σ : Representation k D E) [IsIrreducible σ]
    (τ : Representation k A V) (φ : A →* D)
    (hc : ∀ a d, τ a * ρ d = ρ (φ a * d * (φ a)⁻¹) * τ a)
    (a : A) (v : V) (hv : v ∈ (Subrepresentation.ofSubmodule'
      (isotypicComponent k[D] ρ.asModule σ.asModule)).toSubmodule) :
    τ a v ∈ (Subrepresentation.ofSubmodule'
      (isotypicComponent k[D] ρ.asModule σ.asModule)).toSubmodule := by
  have hu := isotypic_stable_of_commute ρ σ (innerUntwist ρ τ φ hc a)
    (innerUntwist_commute ρ τ φ hc a) v hv
  rw [innerUntwist_reconstruct ρ τ φ hc a]
  let S := Subrepresentation.ofSubmodule' (isotypicComponent k[D] ρ.asModule σ.asModule)
  exact S.apply_mem_toSubmodule (φ a) hu
end Representation.SchurCopies
