module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Reduction

/-!
# Section 3 and Section 5 counting obligations

These contracts separate the two source arguments still needed for the action
counting theorem. `ActionSectionThree` states the distinguished point-swapping,
odd-core, and Sylow counting facts of Lemma 3.4 and Propositions 3.5--3.8.
`ActionSaturationSeeds` is the first assertion of Corollary 5.7 transported to
the chosen base involution. It has not yet imposed the commutator condition
of (6A); `Counting.Saturation` constructs that condition without changing the
prime, involution, or inverted cardinality.

These are proof obligations, not assertions that the source results are proved.
Sylow subgroups and odd cores are taken inside the displayed local subgroup;
no ambient strong embedding or normality of that subgroup is assumed.

Source: GLS, Volume 4, Chapter 2, printed pp. 28--31, 39--42.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The Section 3 inputs used by the Section 5 proof. -/
public structure ActionSectionThree (Z : Set G) (M : Subgroup G) : Prop where
  /-- Lemma 3.4(c); the involution also interchanges the two points. -/
  swap : ∀ beta gamma : G ⧸ M, beta ≠ gamma →
    ∃ t ∈ Z, t • beta = gamma
  /-- The consequence of Proposition 3.5 used in the proof of 3.7. -/
  swapping_core : ∀ t ∈ Z, ∀ beta : G ⧸ M, t • beta ≠ beta →
    ∀ W : Subgroup G,
      W ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta) →
      t ∈ Subgroup.normalizer (W : Set G) →
      ⁅W, Subgroup.zpowers t⁆ ≤ (pPrimeCore 2 W).map W.subtype
  /-- Proposition 3.7(a,b): invariant Sylow extension containing a Sylow
  subgroup of the local centralizer. -/
  swapping_sylow : ∀ t ∈ Z, ∀ beta : G ⧸ M, t • beta ≠ beta →
    ∀ (p : ℕ), p.Prime → Odd p → ∀ W P : Subgroup G,
      W ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta) →
      t ∈ Subgroup.normalizer (W : Set G) → IsPGroup p P → P ≤ W →
      t ∈ Subgroup.normalizer (P : Set G) →
      ∃ Q : Subgroup G, theorem4bIsSylowSubgroupOf p Q W ∧ P ≤ Q ∧
        t ∈ Subgroup.normalizer (Q : Set G) ∧
        ∃ R : Subgroup G,
          theorem4bIsSylowSubgroupOf p R (W ⊓ Subgroup.centralizer ({t} : Set G)) ∧
          R ≤ Q
  /-- Proposition 3.7(c,d), with the global parameter based at any `z ∈ Z ∩ M`. -/
  swapping_bound : ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z,
    ∀ beta : G ⧸ M, t • beta ≠ beta → ∀ (p : ℕ), p.Prime → Odd p →
    ∀ P : Subgroup G, IsPGroup p P →
      P ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta) →
      t ∈ Subgroup.normalizer (P : Set G) →
      theorem4bInvertedCard t P ≤ theorem4bPrimeShare M z p ∧
        (theorem4bIsSylowSubgroupOf p P
          (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta)) →
          theorem4bInvertedCard t P = theorem4bPrimeShare M z p)
  /-- Proposition 3.8(b), retaining membership in the distinguished set. -/
  base_bound : ∀ z ∈ Z, z ∈ M → ∀ (p : ℕ), p.Prime → Odd p →
    ∀ beta : G ⧸ M, beta ≠ QuotientGroup.mk 1 →
    ∀ P : Subgroup G, IsPGroup p P → P ≤ M ⊓ MulAction.stabilizer G beta →
      z ∈ Subgroup.normalizer (P : Set G) →
      theorem4bInvertedCard z P ≤ theorem4bPrimeShare M z p ∧
        (theorem4bIsSylowSubgroupOf p P (M ⊓ MulAction.stabilizer G beta) →
          theorem4bInvertedCard z P = theorem4bPrimeShare M z p)
  /-- Proposition 3.8(c), equivalence of its first and third assertions. -/
  invariant_sylow : ∀ z ∈ Z, z ∈ M → ∀ p : ℕ, p.Prime → Odd p →
    ∀ beta : G ⧸ M, beta ≠ QuotientGroup.mk 1 →
      ((∃ Q : Subgroup G,
          theorem4bIsSylowSubgroupOf p Q (M ⊓ MulAction.stabilizer G beta) ∧
          z ∈ Subgroup.normalizer (Q : Set G)) ↔
        ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ M ⊓ MulAction.stabilizer G beta ∧
          z ∈ Subgroup.normalizer (P : Set G) ∧
          theorem4bInvertedCard z P = theorem4bPrimeShare M z p)

/-- Corollary 5.7 after conjugating its involution to the specified `z`.
The subgroup still fixes at least three points. No nontriviality or
commutator-generation condition is imposed here. -/
@[expose] public def ActionSaturationSeeds (Z : Set G) (M : Subgroup G) : Prop :=
  ∀ z ∈ Z, z ∈ M → ∀ p : ℕ, p.Prime → Odd p →
    ¬ MulAction.IsMultiplyPretransitive G (G ⧸ M) 2 →
    ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ M ∧
      z ∈ Subgroup.normalizer (P : Set G) ∧
      3 ≤ Nat.card (theorem4bFixedPoints M P) ∧
      theorem4bInvertedCard z P = theorem4bPrimeShare M z p

end BenderSuzuki.ZD
