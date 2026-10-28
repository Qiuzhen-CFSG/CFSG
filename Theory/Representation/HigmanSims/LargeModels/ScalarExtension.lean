module

public import Theory.Representation.HigmanSims.LargeModels.Inputs
public import Theory.Representation.InjectiveDescent
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Scalar extension of the large HS model inputs

Absolute irreducibility of the finite-field actions gives irreducibility over
every extension field. For the equal-degree pair, embed its finite coefficient
field into the algebraically closed target. The unequal traces remain unequal
under this embedding, so the extended actions cannot be equivalent.

These lemmas apply to the literal HS carrier and retain the three finite
construction inputs explicitly. They supply the coefficient-field step in the
seven-model saturation argument; they do not assert existence of the inputs.
Candidate provenance and source references are in `LargeModels.Inputs`.
-/

public section
namespace Representation.HigmanSims.LargeModels

open Sporadic.LeechRelated.HS

private theorem mapCoefficients_irreducible
    {k F : Type*} [Field k] [Field F] {n : ℕ}
    (f : k →+* F) (ρ : Representation k Carrier (Fin n → k))
    (h : ρ.IsAbsolutelyIrreducible) :
    (mapCoefficients f ρ).IsIrreducible := by
  let : Algebra k F := f.toAlgebra
  let := h
  exact (extendScalarsMapCoefficientsEquiv (E := F) ρ).irreducible_euqiv.mp
    (IsAbsolutelyIrreducible.irreducible_of_extension ρ F)

/-- The four binary models extend to any characteristic-two field, preserving
their specified coordinate dimensions. -/
theorem binaryModels_over_field (h : BinaryModelsExist) (hs : IsSimpleGroup Carrier)
    (F : Type*) [Field F] [CharP F 2] :
    ∃ ρ : ∀ i, Representation F Carrier (Fin (binaryDegree i) → F),
      ∀ i, (ρ i).IsIrreducible := by
  obtain ⟨σ, hi⟩ := h hs
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact ⟨fun i => mapCoefficients (algebraMap (ZMod 2) F) (σ i),
    fun i => mapCoefficients_irreducible _ _ (hi i)⟩

/-- A finite-field trace witness separates the two degree-896 models over
every algebraically closed characteristic-two field. -/
theorem traceSeparatedPair_over_field (h : TraceSeparatedPairExists)
    (hs : IsSimpleGroup Carrier) (F : Type*) [Field F] [CharP F 2] [IsAlgClosed F] :
    ∃ ρ₁ ρ₂ : Representation F Carrier (Fin 896 → F),
      ρ₁.IsIrreducible ∧ ρ₂.IsIrreducible ∧ IsEmpty (ρ₁.Equiv ρ₂) := by
  obtain ⟨k, _, _, _, σ₁, σ₂, hi₁, hi₂, g, htrace⟩ := h hs
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let f : k →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := k) (M := F)).toRingHom
  refine ⟨mapCoefficients f σ₁, mapCoefficients f σ₂,
    mapCoefficients_irreducible f σ₁ hi₁, mapCoefficients_irreducible f σ₂ hi₂, ?_⟩
  refine ⟨fun e => htrace (f.injective ?_)⟩
  have he := congrFun (char_iso e) g
  change LinearMap.trace F _ (mapCoefficients f σ₁ g) =
    LinearMap.trace F _ (mapCoefficients f σ₂ g) at he
  simpa only [mapCoefficients_trace] using he

/-- Absolute irreducibility of the degree-1408 restriction is the input;
extension preserves it on the same HS carrier. -/
theorem restrictedModel_over_field (h : RestrictedModelExists) (hs : IsSimpleGroup Carrier)
    (F : Type*) [Field F] [CharP F 2] :
    ∃ ρ : Representation F Carrier (Fin 1408 → F), ρ.IsIrreducible := by
  obtain ⟨σ, hi⟩ := h hs
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact ⟨mapCoefficients (algebraMap (ZMod 2) F) σ, mapCoefficients_irreducible _ _ hi⟩

end Representation.HigmanSims.LargeModels
