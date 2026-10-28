module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Contracts

/-!
# Local normalizer inputs for Proposition 5.2

These are explicit outstanding local-group obligations, not assertions of
Proposition 5.2. For an odd subgroup failing to fix a distinguished involution's
point, Lemma 3.13 gives rank one for the distinguished-generated part of its
normalizer. Local conjugacy and the Z-star theorem supply the other two clauses.
The counting argument uses these to prove Lemmas 5.4--5.6.

The rank refers to the closure of the distinguished set *inside* the normalizer;
the odd core is also internal to the normalizer. No ambient strong embedding
or rank restriction on the entire normalizer is imposed.

Source: GLS, Volume 4, Chapter 2, Lemma 3.13 and the paragraph preceding (5A).
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Local structure needed only in the contrary-to-fixed-point branch. -/
public structure SectionFiveNormalizerStructure (Z : Set G) (P : Subgroup G) : Prop where
  rank : ¬ TwoRankAtLeastTwo
    (Subgroup.closure ((Subgroup.normalizer (P : Set G)).subtype ⁻¹' Z))
  one_class : ∀ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) →
    ∀ t ∈ Z, t ∈ Subgroup.normalizer (P : Set G) →
    ∃ g : Subgroup.normalizer (P : Set G), MulAut.conj (g : G) s = t
  factor : ∀ s : Subgroup.normalizer (P : Set G), (s : G) ∈ Z →
    pPrimeCore 2 (Subgroup.normalizer (P : Set G)) ⊔
      Subgroup.centralizer ({s} : Set (Subgroup.normalizer (P : Set G))) = ⊤

end BenderSuzuki.ZD
