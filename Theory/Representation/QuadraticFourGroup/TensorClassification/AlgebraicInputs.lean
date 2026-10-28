module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.FixedPoints

/-!
# The two algebraically closed inputs to natural-tensor classification

`HasIrreducibleProductFactors` asks for an actual external tensor equivalence
with two irreducible coordinate representations. `CubicNaturalClassification`
asks that each cubic-fixed-point-free irreducible factor be an actual
Frobenius natural module. These are explicit mathematical proof obligations,
not asserted classification theorems.

Their consumer transfers the cubic hypotheses to the factors and tensors the
resulting intertwiners. This isolates two independent inputs of GLS2,
Theorem 25.14, Step 5 (ChapterG.tex, lines 906--928). Both inputs still have
to be proved over the algebraically closed Schur field before the source
prerequisite is complete.
-/

@[expose] public section

namespace Representation.QuadraticFourGroup.TensorClassification

variable {n : ℕ} {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

/-- A concrete irreducible external-tensor decomposition over one field. -/
def HasIrreducibleProductFactors (ρ : Representation F (Factor n × Factor n) W) : Prop :=
  ∃ (d₁ d₂ : ℕ) (τ₁ : Representation F (Factor n) (Fin d₁ → F))
    (τ₂ : Representation F (Factor n) (Fin d₂ → F)),
    τ₁.IsIrreducible ∧ τ₂.IsIrreducible ∧ Nonempty (ρ.Equiv (externalTensor τ₁ τ₂))

/-- The single-factor classification, with actual twisted natural matrices. -/
def CubicNaturalClassification (e : GaloisField 2 n →+* F) : Prop :=
  ∀ (d : ℕ) (τ : Representation F (Factor n) (Fin d → F)),
    τ.IsIrreducible → CubicFixedPointFree τ →
      ∃ i : ℕ, i < n ∧ Nonempty (τ.Equiv (mappedFrobeniusNatural e i))

/-- Apply the two independent classification inputs to the literal factor actions. -/
theorem exists_naturalTensor_equiv_of_factors
    (ρ : Representation F (Factor n × Factor n) W)
    (e : GaloisField 2 n →+* F) (h : CubicFreeOnFactors ρ)
    (hprod : HasIrreducibleProductFactors ρ) (hnat : CubicNaturalClassification e) :
    ∃ i j : ℕ, i < n ∧ j < n ∧
      Nonempty (ρ.Equiv
        (externalTensor (mappedFrobeniusNatural e i) (mappedFrobeniusNatural e j))) := by
  obtain ⟨d₁, d₂, τ₁, τ₂, h₁, h₂, ⟨φ⟩⟩ := hprod
  let := h₁
  let := h₂
  let : Nontrivial (Fin d₁ → F) := Subrepresentation.irreducible_module_nontrivial τ₁
  let : Nontrivial (Fin d₂ → F) := Subrepresentation.irreducible_module_nontrivial τ₂
  have hc := (h.of_equiv φ).factors
  obtain ⟨i, hi, ⟨ei⟩⟩ := hnat d₁ τ₁ h₁ hc.1
  obtain ⟨j, hj, ⟨ej⟩⟩ := hnat d₂ τ₂ h₂ hc.2
  exact ⟨i, j, hi, hj, ⟨φ.trans (externalTensorEquiv ei ej)⟩⟩

end Representation.QuadraticFourGroup.TensorClassification

end
