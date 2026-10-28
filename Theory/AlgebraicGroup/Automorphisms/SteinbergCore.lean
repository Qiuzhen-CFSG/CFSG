module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg

universe u

/-!
Composition and uniqueness cores for the Steinberg generator formula.

These statements isolate the part of GLS3 §1.15 that follows formally from a
supplied scalar system and a generating family of root elements.  Existence of
the algebraic Frobenius (and the exceptional graph--field maps) is a separate
geometric construction and is intentionally not inferred here.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- A realization by a Steinberg endomorphism gives membership in the
abstract Steinberg automorphism set. -/
public lemma mem_steinbergAutomorphismSet_of_realization
    {K : Variety k} [AlgebraicGroup K]
    {σ : Aut K} {f : AlgebraicEndomorphism K}
    (hσ : IsAlgebraicRealization σ f)
    (hf : IsAlgebraicSteinbergEndomorphism f) :
    σ ∈ SteinbergAutomorphismSet K :=
  ⟨f, hσ, hf⟩

/-- The Frobenius generator formula determines an abstract automorphism once
the Chevalley root elements generate the point group. -/
public lemma frobeniusAutomorphism_eq_of_chevalleyRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (F : FrobeniusScalarSystem (k := k) (ringChar k))
    (a : ℤ) {φ ψ : Aut K}
    (hgen : HasChevalleyRootGeneration D C)
    (hφ : IsFrobeniusGeneratorFormula D C F a φ)
    (hψ : IsFrobeniusGeneratorFormula D C F a ψ) :
    φ = ψ := by
  apply automorphism_eq_of_chevalleyRootGeneration D C hgen
  intro α t
  rw [hφ, hψ]

/-- Exponents add under composition of automorphisms satisfying the same
Frobenius scalar system. -/
public lemma frobeniusGeneratorFormula_mul
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (F : FrobeniusScalarSystem (k := k) (ringChar k))
    {a b : ℤ} {φ ψ : Aut K}
    (hφ : IsFrobeniusGeneratorFormula D C F a φ)
    (hψ : IsFrobeniusGeneratorFormula D C F b ψ) :
    IsFrobeniusGeneratorFormula D C F (a + b) (φ * ψ) := by
  intro α t
  change φ (ψ (C.x α t)) = C.x α (F.scalar (a + b) t)
  rw [hψ α t, hφ α (F.scalar b t)]
  rw [F.add]

end

end Theory.AlgebraicGroup
