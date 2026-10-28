module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts

/-!
# The maximal prime-share subgroup in Proposition 5.2

This is the remaining local-group proof obligation, not a proved source result.
The candidate conditions are exactly Proposition 5.2(i,ii): a p-subgroup with
at least three fixed points and a distinguished normalizing involution whose
inverted set has the global p-share cardinality. Maximality is among all such
subgroups of the ambient group, with the prime and global parameter fixed.

The conclusion says that every distinguished involution in the normalizer has
its unique fixed point fixed by the subgroup. No ambient strong embedding is
assumed. Proposition 5.2(b) is not needed at this interface.

Source: GLS, Volume 4, Chapter 2, Proposition 5.2(a) and Lemmas 5.4--5.6,
printed pp. 39--41; `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conditions (i,ii) of Proposition 5.2, keeping its global parameter based
at the displayed involution z in M. -/
@[expose] public def actionPrimeShareCandidate
    (Z : Set G) (M : Subgroup G) (z : G) (p : ℕ) (P : Subgroup G) : Prop :=
  IsPGroup p P ∧ 3 ≤ Nat.card (theorem4bFixedPoints M P) ∧
    ∃ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) ∧
      theorem4bInvertedCard s P = theorem4bPrimeShare M z p

/-- The precise local fixed-point implication required from Proposition 5.2(a).
This definition records an obligation that its source proof must discharge. -/
@[expose] public def ActionPrimeShareMaximalFixes
    (Z : Set G) (M : Subgroup G) : Prop :=
  ∀ z ∈ Z, z ∈ M → ∀ p : ℕ, p.Prime → Odd p →
    ∀ P : Subgroup G, Maximal (actionPrimeShareCandidate Z M z p) P →
      ∀ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) →
        ∀ beta : G ⧸ M, s • beta = beta → P ≤ MulAction.stabilizer G beta

end BenderSuzuki.ZD
