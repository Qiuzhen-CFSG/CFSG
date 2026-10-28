module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.CyclicOrder
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Nontrivial
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.FrobeniusReduction

/-!
# Assembly of the exceptional Ree tensor classification

The coefficient embedding is injective and matches the concrete algebraic root
curves. Given genuine Steinberg factorization, restriction irreducibility and
parameter uniqueness, coefficient Frobenius gives the character period and the
shift of factor dimensions. Faithfulness supplies a nontrivial factor through
the explicit paired end-root element of the Ree group.

The theorem below is a conditional assembly. Existence of the exceptional
factorization, its restriction and uniqueness theorems, and coefficient-Frobenius
compatibility still require proofs; this module does not assert the
unconditional source theorem.

Source: GLS3, Definition 2.8.1(b), Theorems 2.8.2 and 2.8.5, Corollary
2.8.6(b), and Remark 2.8.8; Steinberg, *Endomorphisms of Linear Algebraic
Groups*, Theorems 13.1 and 13.3. There are `2*k+1` exceptional factors for
the field of size `2^(2*k+1)`, and ordinary Frobenius shifts indices by two.
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] {k : ℕ}

/-- The remaining consequences of a genuine exceptional Steinberg
factorization, with all still-needed representation-theoretic inputs explicit. -/
theorem factorization_consequences
    {W : Type v} [AddCommGroup W] [Module F W]
    (σ : Representation F (Model k) W) (hσ : Function.Injective σ)
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (hirr : ∀ B : ZMod (2 * k + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) → Representation.IsIrreducible (exceptionalTensor ι B).ρ)
    (hunique : ∀ B C : ZMod (2 * k + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Representation.Equiv (exceptionalTensor ι B).ρ (exceptionalTensor ι C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (hbasic : ∀ i, (B i).IsExceptionalBasic)
    (e : Representation.Equiv σ (exceptionalTensor ι B).ρ)
    (hFrob : ∀ (r : ℕ) (g : Model k),
      Representation.character (exceptionalTensor ι B).ρ g ^ (2 ^ r) =
        Representation.character (exceptionalTensor ι (shiftFactors B r)).ρ g) :
    (∃ i, (B i).IsNontrivial) ∧
    (∀ g, σ.character g ^ (2 ^ (2 * k + 1)) = σ.character g) ∧
    (∀ r : ℕ, (∀ g, σ.character g ^ (2 ^ r) = σ.character g) →
      ∀ i, Module.finrank F (B (i + 2 * (r : ZMod (2 * k + 1)))).Space =
        Module.finrank F (B i).Space) := by
  obtain ⟨hfixed, hperiod⟩ := character_fixed_and_factor_period_of_shift
    ι hirr hunique B hbasic hFrob
  have hchar := Representation.char_iso e
  refine ⟨exists_nontrivial_factor_of_faithful σ hσ ι B e, ?_, ?_⟩
  · simpa only [hchar] using hfixed
  · simpa only [hchar] using hperiod

end ReeF4.BinaryDegree.ExceptionalTensor.Classification
