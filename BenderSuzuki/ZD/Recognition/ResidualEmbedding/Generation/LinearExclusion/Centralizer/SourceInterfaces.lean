module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.NormalizerGeometry

/-!
# Remaining source inputs for the proper linear centralizer count

These interfaces describe the separate mathematical obligations of GLS IV,
Chapter 2, Lemmas 15.2(a,c) and 15.3–15.5. They are explicit premises for
independent conditional proofs of the later counting argument, not assertions
that those earlier source lemmas have been proved. The original Context has
none of these fields and remains unchanged.

The two-core is always the actual O₂(C_G(L)), with its subtype image in G.
The group V is the subtype image of O₂(M), and the centralizer is C_M(A).
All statements retain these literal groups and the original model parameter.
The final centralizer assembly must construct both interfaces before applying
the conditional Lemma 15.6 result.

Source: refs/KGroup/GLS4/Chapter2.tex, Lemmas 15.2–15.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ}

/-- The remaining model and normalizer assertions of Lemma 15.2.
The normalizer clause applies to every nontrivial subgroup, including odd ones. -/
public structure CentralizerLocalModelData (d : Context Z M z t n) where
  embedding : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t
  embedding_injective : Function.Injective embedding
  normalizer_le : ∀ Y : Subgroup G,
    Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
      normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G)

/-- Precisely the earlier two-core structure consumed by the source count.
Its construction requires the genuine arguments of Lemmas 15.3–15.5. -/
public structure CentralizerLocalTwoData (d : Context Z M z t n) : Prop where
  twoCore_ne_bot : pCore 2 (centralizer (residualGenerated M z t : Set G)) ≠ ⊥
  twoCore_sylow : ∃ S : Sylow 2 (centralizer (residualGenerated M z t : Set G)),
    (S : Subgroup (centralizer (residualGenerated M z t : Set G))) =
      pCore 2 (centralizer (residualGenerated M z t : Set G))
  twoCore_elementary : IsElementaryAbelian 2
    ((pCore 2 (centralizer (residualGenerated M z t : Set G))).map
      (centralizer (residualGenerated M z t : Set G)).subtype)
  pair_core_eq : residualPairStabilizer M t ⊓ (pCore 2 M).map M.subtype =
    (pCore 2 (centralizer (residualGenerated M z t : Set G))).map
      (centralizer (residualGenerated M z t : Set G)).subtype
  pair_involutions : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    v ∈ (pCore 2 (centralizer (residualGenerated M z t : Set G))).map
      (centralizer (residualGenerated M z t : Set G)).subtype
  centralizer_odd_supplement : ∃ Y : Subgroup G,
    Y ≤ centralizer (residualGenerated M z t : Set G) ∧ Odd (Nat.card Y) ∧
      ((M ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
        ((pCore 2 M).map M.subtype : Set G) * (Y : Set G)

end BenderSuzuki.ZD.LinearExclusion
