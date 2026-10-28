module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.Reduction

/-!
# Simplicity certification interface for the explicit J₄ matrix carrier

The final normal-subgroup argument reduces to two independent certificates:
every prime-order element has a conjugate power among the twelve specified
words, and each of those words normally generates the concrete matrix group.
Cauchy's theorem then rules out every nontrivial proper normal subgroup.

This module proves that reduction; it does not yet discharge the two structural
certificates and therefore does not declare an `IsSimpleGroup Model` instance.
The representative words and their ATLAS source are documented in `Words`.
-/

public section

namespace Janko4.Simplicity

/-- Simplicity of the actual generated carrier from explicit structural certificates.
The order hypothesis is used only to establish nontriviality. -/
theorem isSimpleGroup_of_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (hcover : ∀ x : Model, (orderOf x).Prime →
      ∃ (i : Fin 12) (k : ℕ) (g : Model),
        primeRepresentative (a hA) (b hB) i = g * x ^ k * g⁻¹)
    (hgenerate : ∀ i : Fin 12,
      Subgroup.normalClosure ({primeRepresentative (a hA) (b hB) i} : Set Model) = ⊤) :
    IsSimpleGroup Model := by
  have : Nontrivial Model := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  exact isSimpleGroup_of_prime_representatives _ hcover hgenerate

end Janko4.Simplicity
