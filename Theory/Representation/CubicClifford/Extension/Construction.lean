module

public import Theory.Representation.CubicClifford.HomogeneousDimension

/-!
# Tensor decomposition from an extending constituent

Let `K` be normal in a finite group `H`. If an absolutely irreducible constituent
of an irreducible binary `H`-module `V` extends to an `H`-module `E`, then the
finite-dimensional space `Hom_K(E,V)` carries an irreducible `H/K`-action, and
evaluation gives an actual `H`-equivalence `E ⊗ Hom_K(E,V) ≃ V`.

The action and surjectivity of evaluation come from `Extension`; the Clifford
direct sum and scalar endomorphisms give the dimension equality and
irreducibility in `HomogeneousDimension`. Here these results discharge every
premise of the evaluation isomorphism. Occurrence and the resulting tensor
isomorphism use Mathlib's `Representation.Equiv`.

This is the conditional representation-theoretic construction used in the proof
of Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.21(1), printed
pp.956–957. The cubic multiplicity and concrete constituent identifications are
separate from this construction.
-/

public section

open scoped TensorProduct

namespace Representation.CubicClifford

universe u v w

variable {H : Type u} [Group H] [Finite H] (Ksub : Subgroup H) [Ksub.Normal]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {E : Type w} [AddCommGroup E] [Module (ZMod 2) E]
  (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H V)

section Occurrence

variable [IsIrreducible ρ] [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
  (hσabs : IsAbsolutelyIrreducible (τ.comp Ksub.subtype))
  (A : Subrepresentation (ρ.comp Ksub.subtype))
  (hA : Nonempty (Representation.Equiv A.toRepresentation (τ.comp Ksub.subtype)))

include hσabs hA

/-- An actual occurrence of an extending absolutely irreducible constituent
makes evaluation bijective, with no dimension or homogeneity assumption. -/
theorem evaluation_bijective_of_occurrence :
    Function.Bijective (evaluation Ksub τ ρ) := by
  have hA' := hA.map RepEquiv.ofRepresentationEquiv
  have hsurj := evaluation_surjective_of_occurrence Ksub τ ρ hσabs A hA'
  have hdim := homogeneous_finrank Ksub τ ρ hσabs A hA'
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj,
    hsurj⟩

/-- Evaluation is an equivalence of the actual `H`-representations. -/
noncomputable def evaluationEquiv :
    Representation.Equiv (τ.tprod (homRepresentation Ksub τ ρ)) ρ :=
  (Representation.IntertwiningMap.mk (evaluation Ksub τ ρ)
    (evaluation_intertwining Ksub τ ρ)).ofBijective
      (evaluation_bijective_of_occurrence Ksub τ ρ hσabs A hA)

@[simp] theorem evaluationEquiv_tmul (e : E) (f : homSpace Ksub τ ρ) :
    evaluationEquiv Ksub τ ρ hσabs A hA (e ⊗ₜ[ZMod 2] f) = f.1 e := by
  rfl

/-- The canonical finite-dimensional multiplicity space is irreducible, is
annihilated by `Ksub`, and gives the tensor decomposition of `ρ`.
Its finite-dimensional instance is `homSpace_finiteDimensional`. -/
theorem extension_tensor_decomposition :
    IsIrreducible (homRepresentation Ksub τ ρ) ∧
      Ksub ≤ (homRepresentation Ksub τ ρ).ker ∧
      Nonempty (Representation.Equiv ρ (τ.tprod (homRepresentation Ksub τ ρ))) := by
  exact ⟨homRepresentation_irreducible Ksub τ ρ hσabs A
      (hA.map RepEquiv.ofRepresentationEquiv),
    homSubgroup_le_ker Ksub τ ρ, ⟨(evaluationEquiv Ksub τ ρ hσabs A hA).symm⟩⟩

/-- The constructed multiplicity representation is irreducible over `H/Ksub`. -/
theorem homQuotientRepresentation_irreducible :
    IsIrreducible (homQuotientRepresentation Ksub τ ρ) :=
  (homQuotientRepresentation_irreducible_iff Ksub τ ρ).mpr
    (extension_tensor_decomposition Ksub τ ρ hσabs A hA).1

end Occurrence

omit [Finite H] in
/-- Inflation of the quotient action recovers the constructed `H`-action. -/
@[simp] theorem homQuotientRepresentation_comp :
    (homQuotientRepresentation Ksub τ ρ).comp (QuotientGroup.mk' Ksub) =
      homRepresentation Ksub τ ρ := rfl

end Representation.CubicClifford
