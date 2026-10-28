module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts

/-!
# Local and index obligations for distinguished Section 3 counting

The remaining geometric inputs are separated from the finite Sylow arithmetic.
`SectionThreeLocal` asks for the relative odd core and invariant Sylow results
of Propositions 3.5 and 3.7(a,b). `SectionThreeIndices` asks for the two index
identities in Proposition 3.6(d). These are explicit proof obligations; no
constructor from minimality is asserted in this module. In particular no
oddness of the whole two-point stabilizer is assumed.

Source: GLS, Volume 4, Chapter 2, printed pp.29--31.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The local Z-star and Sylow obligations, before the numerical count. -/
public structure SectionThreeLocal (Z : Set G) (M : Subgroup G) : Prop where
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

/-- The two centralizer-index identities of Proposition 3.6(d). -/
public structure SectionThreeIndices (Z : Set G) (M : Subgroup G) : Prop where
  /-- Index at the involution interchanging the points. -/
  swapping : ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z, ∀ beta : G ⧸ M,
    t • beta ≠ beta →
    let D := MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta)
    ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z
  /-- Index at the distinguished involution fixing the base point. -/
  base : ∀ z ∈ Z, z ∈ M → ∀ beta : G ⧸ M,
    beta ≠ QuotientGroup.mk 1 →
    let D := M ⊓ MulAction.stabilizer G beta
    ((D ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf D).index = theorem4bM M z

end BenderSuzuki.ZD
