module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelTypes
public import Theory.GroupTheory.QuasithinBasic

/-!
# Concrete rank-witness contracts for the higher-field sieve

These two independent inputs specify precisely the six rank inequalities
needed to eliminate the excluded matrix groups. They are proof obligations,
not classification hypotheses from the source. Each inequality must be
established by genuine group calculations. The conditional assembly in
`ModelReduction` consumes them; the unconditional assembly must construct
both inputs.

Source: Aschbacher–Smith, proof of 13.8.20(a), printed p.954 (PDF p.971).
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction

/-- Rank-two witnesses for the special and projective signed-three cases.
The unitary field is the coefficient field, of order `(2^n)^2`. -/
structure SignedThreeRanks : Prop where
  linear_special : ∀ (F : Type) [Field F] [Finite F] (n : ℕ),
    1 < n → Nat.card F = 2 ^ n → Even n → 2 ≤ primeRank 3 SL(3,F)
  linear_projective : ∀ (F : Type) [Field F] [Finite F] (n : ℕ),
    1 < n → Nat.card F = 2 ^ n → Even n → 2 ≤ primeRank 3 PSL(3,F)
  unitary_special : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F) (n : ℕ),
    1 < n → Nat.card F = (2 ^ n) ^ 2 → (∀ x, J.conj x = x ^ (2 ^ n)) →
      Odd n → 2 ≤ primeRank 3 J.specialSubgroup
  unitary_projective : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F) (n : ℕ),
    1 < n → Nat.card F = (2 ^ n) ^ 2 → (∀ x, J.conj x = x ^ (2 ^ n)) →
      Odd n → 2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J)

/-- Rank-two witnesses in the actual commutator carriers. -/
structure DerivedRanks : Prop where
  symplectic : ∀ (F : Type) [Field F] [Finite F] (n : ℕ),
    1 < n → Nat.card F = 2 ^ n →
      2 ≤ primeRank 3 (commutator (Matrix.symplecticGroup (Fin 2) F))
  g2 : ∀ (F : Type) [Field F] [Finite F] (n : ℕ),
    1 < n → Nat.card F = 2 ^ n →
      2 ≤ primeRank 3 (commutator (Atlas.G2.Model F))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction

end
