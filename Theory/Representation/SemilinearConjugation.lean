module

public import Mathlib.RepresentationTheory.Character
public import Theory.LinearAlgebra.SemilinearTrace

/-!
# Semilinear conjugation of representations

Conjugation through a semilinear equivalence transports the representation
and its lattice of invariant subspaces. It preserves irreducibility and
applies the field automorphism to the character, by the semilinear trace
formula. Coordinatewise field automorphisms supply such equivalences on
finite coordinate spaces.

This is the representation-theoretic construction behind Galois conjugation
of characters, used in Wong (1964), Appendix (b), p. 109.
-/

public section

noncomputable section

namespace Representation

variable {F G V W : Type*} [Field F] [Monoid G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

variable (σ : F ≃+* F)
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Transport a representation through a semilinear equivalence. -/
@[expose] def semilinearConjugate (ρ : Representation F G V)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V W) :
    Representation F G W :=
  e.conjRingEquiv.toMonoidHom.comp ρ

@[simp]
theorem semilinearConjugate_apply (ρ : Representation F G V)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V W)
    (g : G) (w : W) : semilinearConjugate σ ρ e g w = e (ρ g (e.symm w)) := rfl

/-- Semilinear conjugation identifies the lattices of invariant subspaces. -/
def semilinearConjugateSubrepresentationEquiv (ρ : Representation F G V)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V W) :
    Subrepresentation ρ ≃o Subrepresentation (semilinearConjugate σ ρ e) where
  toFun S :=
    { toSubmodule := S.toSubmodule.comap e.symm.toLinearMap
      apply_mem_toSubmodule g w hw := by
        change e.symm (e (ρ g (e.symm w))) ∈ S.toSubmodule
        simpa using S.apply_mem_toSubmodule g hw }
  invFun S :=
    { toSubmodule := S.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule g v hv := by
        have h := S.apply_mem_toSubmodule g hv
        simpa using h }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext w
    simp
  map_rel_iff' := by
    intro S T
    change (∀ w, e.symm w ∈ S.toSubmodule → e.symm w ∈ T.toSubmodule) ↔ S ≤ T
    constructor
    · intro h v hv
      change v ∈ T.toSubmodule
      have hv' : v ∈ S.toSubmodule := hv
      simpa using h (e v) (by simpa using hv')
    · intro h w hw
      exact h hw

/-- Irreducibility is preserved by semilinear conjugation. -/
theorem isIrreducible_semilinearConjugate (ρ : Representation F G V)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V W)
    (hρ : IsIrreducible ρ) : IsIrreducible (semilinearConjugate σ ρ e) :=
  (semilinearConjugateSubrepresentationEquiv σ ρ e).isSimpleOrder_iff.mp hρ

/-- The character of a semilinear conjugate is the conjugated character. -/
theorem character_semilinearConjugate [FiniteDimensional F V] [FiniteDimensional F W]
    (ρ : Representation F G V)
    (e : LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) V W) (g : G) :
    (semilinearConjugate σ ρ e).character g = σ (ρ.character g) :=
  LinearMap.trace_conj_semilinear σ (ρ g) e

/-- Applying a field automorphism to every coordinate is semilinear. -/
def coordinateSemilinearEquiv (ι : Type*) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) (ι → F) (ι → F) where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

/-- The coordinate semilinear equivalence applies the automorphism pointwise. -/
@[simp]
theorem coordinateSemilinearEquiv_apply (ι : Type*) (v : ι → F) (i : ι) :
    coordinateSemilinearEquiv σ ι v i = σ (v i) := by rfl

/-- Its inverse applies the inverse automorphism pointwise. -/
@[simp]
theorem coordinateSemilinearEquiv_symm_apply (ι : Type*) (v : ι → F) (i : ι) :
    (coordinateSemilinearEquiv σ ι).symm v i = σ.symm (v i) := by rfl

end Representation
