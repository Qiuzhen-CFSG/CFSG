module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SmallQuotients

/-!
# The final small-model exclusions in the radical reduction

The intermediate conclusion below is the intersection of the two surviving
1.3.4 model families with the complete C.2.7 list. It is a conclusion to be
proved by the model comparison, not a formulation or an assumption of C.2.7.
In particular the source implication must retain all of C.2.7(a)--(h),
including the linear-three star quotient and its actual action.

Once that comparison is proved, the solvable image of XT excludes both
the A₅-block and the L₂(7) quotient. Thus the only remaining model is the
binary natural block, with every field of `BinaryBlockEmbedding` supplied.
The outside-component construction and the complete model comparison are
separate obligations; neither is asserted by this module.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.514, first paragraph.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding

universe u
variable {G : Type u} [Group G]

/-- The desired output of comparing the full pushing-up list with 1.3.4.
This is not an authorized earlier-source premise: its construction remains
an obligation of the model-comparison proof. The L₂(7) branch does not
assert that K is a block. -/
structure RankOneSieveConclusion (p : ℕ) (T P H₀ K : Subgroup G) : Prop where
  swapped : SwappedFactors T P K
  source_model : SwappedModel p (XiQuotient K)
  models :
    (ChapterC.IsBlock (K.subgroupOf H₀) ∧ ∃ n, ChapterC.IsL2EvenBlock K n) ∨
    (ChapterC.IsBlock (K.subgroupOf H₀) ∧ ChapterC.IsAlternatingBlock K 5) ∨
    ClassicalGroup.IsPSL (XiQuotient K) 2 7

/-- Normalization is already proved for both surviving alternatives.
Only noncontainment remains to upgrade a candidate to the C.2.7 input. -/
theorem ComponentCandidate.toPushingUpComponent [Finite G]
    {κ : GroupClass.{u}} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K) (hout : ¬ K ≤ M) :
    PushingUpComponent κ p T X P M H₀ K :=
  { h with
    outside := h.outside_iff.mpr hout
    radical_normalizes := h.radical_normalizes }

/-- The actual solvable local image eliminates the two small overlaps,
leaving the binary block required by the downstream commuting argument.
This consumes, rather than proves, the complete model-comparison output. -/
theorem PushingUpComponent.binaryBlockEmbedding [Finite G]
    {κ : GroupClass.{u}} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : PushingUpComponent κ p T X P M H₀ K) (hp : 3 < p)
    (hs : RankOneSieveConclusion p T P H₀ K) :
    BinaryBlockEmbedding p T X P H₀ K := by
  rcases hs.models with ⟨hblock, hbinary⟩ | ⟨_, hfive⟩ | hseven
  · exact ⟨h.local_input, h.sylow_two, h.component, h.quasisimple,
      h.alternatives.1, hs.swapped, hs.source_model, h.containment,
      h.radical_normalizes, hblock, hbinary⟩
  · exact (h.toComponentCandidate.not_alternatingFiveBlock hp
      hs.swapped hs.source_model hfive).elim
  · exact (h.toComponentCandidate.not_linearSeven hp
      hs.swapped hs.source_model hseven).elim

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
