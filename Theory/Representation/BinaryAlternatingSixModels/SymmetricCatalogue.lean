module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Duality
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Reduction
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.TensorIncidence
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.VertexQuotients

/-!
# The binary S₆ catalogue and its Steinberg model

Every finite-dimensional irreducible binary representation of the literal S₆
is equivariantly isomorphic to the trivial representation, one of the two
marked natural representations, or their tensor product. The proof uses its
surjection from the flag module: a simple quotient survives on a vertex
coboundary, where the two fifteen-point calculations recognize it, or factors
through top cohomology, which is equivariantly isomorphic to the tensor.

The reexported `tensorHomologyEquiv` identifies the tensor with the genuine
Steinberg construction `topHomologyRepresentation`: the cycle representation
of the actual duad–syntheme building. The bijection `polarFlagEquiv` and its
point and line action equations identify this building with all flags in the
binary symplectic four-space, retaining the literal S₆ action. The comparison
comes from endpoint tensors, the invariant polar pairings, and incidence
duality; `tensorHomologyEquiv_pairing` gives its coordinate formula.

Only irreducibility of the A₆ restriction of the tensor remains an explicit
hypothesis. No catalogue, vertex-quotient alternative or incidence comparison
is assumed. The independent F₄ splitting argument supplies that hypothesis
to the source assembly, which also owns the A₆ catalogue and all of G.5.1.
The marked invariant-line applications below discharge the model premise of
the G.5.2 exclusion and identify its output with the same building homology.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–2,
printed pp.342–343 (PDF pp.353–354).
-/

public section

open Theory.SpecificGroups.SymmetricSix Representation
namespace BinaryAlternatingSix.SymmetricCatalogue

/-- Exhaustion of the binary S₆ simple modules by actual equivariant models,
conditional only on irreducibility of the alternating tensor. -/
theorem classify
    (hTensor : IsIrreducible alternatingTensor)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ] :
    IsSymmetricModel ρ :=
  classify_of_vertex_maps hTensor ρ
    (point_quotient_alternatives ρ) (line_quotient_alternatives ρ)

/-- The G.5.2 marked parabolic hypotheses recognize the tensor; the catalogue
premise of `tensor_of_invariant_lines_of_model` is now discharged. -/
theorem tensor_recognition
    (hTensor : IsIrreducible alternatingTensor)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (h₁ : HasInvariantLine (ρ.comp A6.subtype) a6DuadStabilizer)
    (h₂ : HasInvariantLine (ρ.comp A6.subtype) a6SynthemeStabilizer) :
    Nonempty (ρ.Equiv tensorAction) :=
  tensor_of_invariant_lines_of_model ρ (classify hTensor ρ) h₁ h₂

/-- The recognized representation is the genuine top reduced homology of the
binary symplectic building, with its original S₆ action. -/
theorem homology_recognition
    (hTensor : IsIrreducible alternatingTensor)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (h₁ : HasInvariantLine (ρ.comp A6.subtype) a6DuadStabilizer)
    (h₂ : HasInvariantLine (ρ.comp A6.subtype) a6SynthemeStabilizer) :
    Nonempty (ρ.Equiv topHomologyRepresentation) := by
  obtain ⟨e⟩ := tensor_recognition hTensor ρ h₁ h₂
  exact ⟨e.trans (tensorHomologyEquiv hTensor)⟩

end BinaryAlternatingSix.SymmetricCatalogue
