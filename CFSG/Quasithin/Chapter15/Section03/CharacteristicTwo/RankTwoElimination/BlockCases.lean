module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.ConjugatePair
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface

/-!
# The block alternatives in the rank-two characteristic-two branch

This file is the source-facing boundary between 15.3.16 and the final
normalizer argument.  The subgroup called `W_L` is always the span in
`LocalData.componentSpan`; it is not silently replaced by the omega-centre
used in C.2.7.  Similarly, the quotient in `C27Data` is the quotient of
`LR = L ⊔ R`, while the plus quotient in `Basic` is the quotient of
`L ⊔ R ⊔ Y₊`.

The C.2.7 theorem and the model-specific extension calculations are source
inputs.  They are recorded with their full interfaces (rather than with a
tag saying that a desired block has been eliminated).  The results below
perform the subgroup transport, construct the two `R₂` assertions, use the
actual C.2.7 alternative, and finish each exclusion through the common
conjugate-pair normalizer contradiction.  Thus a consumer must still provide
the model calculations and their subgroup witnesses; no model tag is itself
treated as a theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.16--22,
printed pp.1125--1128, and Lemma C.2.7, printed pp.145--147.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination

open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open Stellmacher

universe u
variable {G : Type u} [Group G]

/-! The relative `R₂` predicate used in this file.  The ambient group is a
subgroup of `G`; this prevents accidentally asserting normality in `G`. -/
structure IsR2Within (W H : Subgroup G) : Prop where
  normal : (W.subgroupOf H).Normal
  elementary : IsElementaryAbelian 2 (W.subgroupOf H)
  reduced : letI := normal
    pCore 2 (H ⧸ centralizer (W.subgroupOf H : Set H)) = ⊥

abbrev LR (d : LocalData G) (L : Subgroup G) : Subgroup G := L ⊔ d.R
abbrev LRplus (d : LocalData G) (L : Subgroup G) : Subgroup G := overgroup d L

/-! The exact earlier clauses used by the rank-two argument.  The two
three-reduced assertions are intentionally separate: C.2.7 acts on its own
`Ω₁(Z(O₂(LR)))`, whereas `W_L` is the span used by the plus action. -/
structure PreliminaryData (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] : Prop where
  hI : I ∈ d.Hplus
  rank_yplus : primeRank 3 d.Yplus = 2
  yc_three_part : 3 ^ (Nat.card (YC d c.L)).factorization 3 = 3
  characteristic_two : HasCharacteristicTwo I
  solvable_control : SolvableInvariantControl d I
  htheta : theta (d.M ⊓ I) = d.Yplus
  hRcentral : d.R ≤ centralizer (d.V : Set G)
  hRnormalizes : d.R ≤ normalizer (c.L : Set G)
  hYnormalizes : d.Yplus ≤ normalizer (c.L : Set G)
  hC : centralizer (d.V : Set G) ≤ d.M
  hcore : c.L.pCoreIn 2 ≤ d.R
  span_LR : d.componentSpan c.L ≤ LR d c.L
  span_LRplus : d.componentSpan c.L ≤ LRplus d c.L
  span_elementary_LR : IsElementaryAbelian 2
    ((d.componentSpan c.L).subgroupOf (LR d c.L))
  span_elementary_LRplus : IsElementaryAbelian 2
    ((d.componentSpan c.L).subgroupOf (LRplus d c.L))
  span_reduced_LR : ∀ hn : ((d.componentSpan c.L).subgroupOf (LR d c.L)).Normal,
    letI := hn
    pCore 2 ((LR d c.L) ⧸ centralizer
      ((d.componentSpan c.L).subgroupOf (LR d c.L) : Set (LR d c.L))) = ⊥
  span_reduced_LRplus : ∀ hn :
      ((d.componentSpan c.L).subgroupOf (LRplus d c.L)).Normal,
    letI := hn
    pCore 2 ((LRplus d c.L) ⧸ centralizer
      ((d.componentSpan c.L).subgroupOf (LRplus d c.L) : Set (LRplus d c.L))) = ⊥
  commutator_JR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆

/-! C.2.7 is kept as a complete conclusion.  In particular, `alternatives`
is not a projection to a binary/nonbinary tag and retains the stabilizer,
offender, and relative-subnormality clauses. -/
structure C27Data (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] where
  source : GroupClass.{u}
  conclusion : Conclusion source (LR d c.L) c.L d.R
    ((d.M ⊓ I) ⊓ c.L)

theorem span_normalizes_LRplus [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (p : PreliminaryData d c) :
    LRplus d c.L ≤ normalizer (d.componentSpan c.L : Set G) := by
  exact overgroup_normalizes_span d p.htheta p.hRcentral
    p.hRnormalizes p.hYnormalizes

private theorem normalizes_span' {A V L : Subgroup G}
    (hL : A ≤ normalizer (L : Set G))
    (hV : A ≤ normalizer (V : Set G)) :
    A ≤ normalizer (localSpan V L : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨l, hl, v, hv, rfl⟩
  refine subset_closure ⟨a * l * a⁻¹, (hL ha l).mp hl,
    a * v * a⁻¹, (hV ha v).mp hv, ?_⟩
  group

theorem span_normalizes_LR [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (p : PreliminaryData d c) :
    LR d c.L ≤ normalizer (d.componentSpan c.L : Set G) := by
  refine sup_le ?_ ?_
  · exact le_normalizer_conjugateSpanBy d.V c.L
  · exact normalizes_span' p.hRnormalizes
      (p.hRcentral.trans (Subgroup.centralizer_le_normalizer _))

theorem span_isR2_LR [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (p : PreliminaryData d c) :
    IsR2Within (d.componentSpan c.L) (LR d c.L) := by
  let hN := span_normalizes_LR d c p
  have hn : ((d.componentSpan c.L).subgroupOf (LR d c.L)).Normal :=
    normal_subgroupOf_of_le_normalizer (by
      simpa only [map_subgroupOf_eq_of_le p.span_LR] using hN)
  exact ⟨hn, p.span_elementary_LR, p.span_reduced_LR hn⟩

theorem span_isR2_LRplus [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (p : PreliminaryData d c) :
    IsR2Within (d.componentSpan c.L) (LRplus d c.L) := by
  let hN := span_normalizes_LRplus d c p
  have hn : ((d.componentSpan c.L).subgroupOf (LRplus d c.L)).Normal :=
    normal_subgroupOf_of_le_normalizer (by
      simpa only [map_subgroupOf_eq_of_le p.span_LRplus] using hN)
  exact ⟨hn, p.span_elementary_LRplus, p.span_reduced_LRplus hn⟩

/-! 15.3.16 and 15.3.17.  The C.2.7 conclusion is consumed at its full
interface; the small `modelCases` projection is used only after the complete
alternative has been obtained. -/
structure Lemma15316 (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] where
  preliminary : PreliminaryData d c
  c27 : C27Data d c

set_option linter.style.haveILetI false in
theorem lemma_15_3_16 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (h : Lemma15316 d c) :
    IsR2Within (d.componentSpan c.L) (LR d c.L) ∧
      IsR2Within (d.componentSpan c.L) (LRplus d c.L) ∧
      c.L = ⁅c.L, elementaryAbelianMaxJ d.R⁆ ∧
      (letI := actionKernel_normal d (L := c.L)
        (span_normalizes_LRplus d c h.preliminary)
       Theory.GroupTheory.IsQuasisimple (plusImage d c.L c.L)) ∧
      ModelCases (LR d c.L) c.L d.R := by
  refine ⟨span_isR2_LR d c h.preliminary,
    span_isR2_LRplus d c h.preliminary,
    h.preliminary.commutator_JR, ?_⟩
  letI : (actionKernel d c.L).Normal :=
    actionKernel_normal d (L := c.L)
      (span_normalizes_LRplus d c h.preliminary)
  refine ⟨component_image_quasisimple d c h.preliminary.hcore
    (h.preliminary.hRcentral) h.preliminary.hC, ?_⟩
  exact h.c27.conclusion.alternatives.modelCases

/-! The three alternatives which survive the rank and C.2.7 comparison.  The
parameter `n` is retained so the even-field restriction is visible. -/
inductive RankTwoAlternative (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Prop
  | l2 (n : ℕ) (hn : Even n) (model : ChapterC.IsL2EvenBlock c.L n)
  | l3 (model : ChapterC.IsLinearTwoBlock c.L 3)
  | l4 (model : ChapterC.IsLinearTwoBlock c.L 4)
  | l5 (model : ChapterC.IsLinearTwoBlock c.L 5)

/-! 15.3.17 is the rank split before any model is eliminated. -/
def RankSplit (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) : Prop :=
  (primeRank 3 c.L = 1 ∧
      (∃ n, Even n ∧ ChapterC.IsL2EvenBlock c.L n) ∨
    primeRank 3 c.L = 1 ∧ ChapterC.IsLinearTwoBlock c.L 3) ∨
  (primeRank 3 c.L = 2 ∧ d.Yplus ≤ c.L) ∨
  (primeRank 3 c.L = 2 ∧ ∃ n, Even n ∧ ChapterC.IsSL3EvenBlock c.L n)

inductive RankSplitSource (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Prop
  | rankOneL2 (hRank : primeRank 3 c.L = 1) (n : ℕ) (hEven : Even n)
      (model : ChapterC.IsL2EvenBlock c.L n)
  | rankOneL3 (hRank : primeRank 3 c.L = 1)
      (model : ChapterC.IsLinearTwoBlock c.L 3)
  | rankTwoContained (hRank : primeRank 3 c.L = 2)
      (hY : d.Yplus ≤ c.L)
  | rankTwoSL3 (hRank : primeRank 3 c.L = 2) (n : ℕ) (hEven : Even n)
      (model : ChapterC.IsSL3EvenBlock c.L n)

structure RankSplitData (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] where
  /-- The rank/model witness supplied by the 15.3.15--17 source calculation.
  The target `RankSplit` is reconstructed below, so this interface does not
  turn 15.3.17 into a record projection. -/
  source : RankSplitSource d c

theorem lemma_15_3_17 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (h : RankSplitData d c) : RankSplit d c := by
  cases h.source with
  | rankOneL2 hRank n hEven model =>
      exact Or.inl (Or.inl ⟨hRank, ⟨n, hEven, model⟩⟩)
  | rankOneL3 hRank model =>
      exact Or.inl (Or.inr ⟨hRank, model⟩)
  | rankTwoContained hRank hY =>
      exact Or.inr (Or.inl ⟨hRank, hY⟩)
  | rankTwoSL3 hRank n hEven model =>
      exact Or.inr (Or.inr ⟨hRank, ⟨n, hEven, model⟩⟩)

/-! A model exclusion is expressed by the actual pair witness needed by the
source proof.  Its conclusion is then a genuine application of the shared
normalizer contradiction, rather than an assumed `False` field.  The
linear-three entry is split between the surviving `L₃(2)` model and the
larger-field exclusion, since the latter is eliminated only after 15.3.22. -/
structure PairWitness (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] where
  Q : Subgroup G
  hQ : Q ≠ ⊥
  hQS : Q ≤ d.S
  t : G
  ht : t ∈ (d.T : Subgroup G)
  htS : t ∉ d.S
  hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2
  hSQ : d.S ≤ normalizer (Q : Set G)
  hLS : c.L ⊔ d.S ≤ normalizer (conjugatePair Q t : Set G)
  hY : d.Y ≤ c.L ⊔ (d.T : Subgroup G)
  hunique : Chapter4.UniqueMaximalOvergroup
    (d.Y ⊔ (d.T : Subgroup G)) d.M

theorem pairWitness_false [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (w : PairWitness d c) : False := by
  exact outside_conjugatePair_contradiction d c.outside w.hQ w.hQS w.t w.ht w.htS
    w.hindex w.hSQ w.hLS w.hY w.hunique

structure ExclusionData (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [Finite G] where
  l2 : ∀ n, ChapterC.IsL2EvenBlock c.L n → PairWitness d c
  a5 : ChapterC.IsAlternatingBlock c.L 5 → PairWitness d c
  sl3 : ∀ n, 1 < n → ChapterC.IsSL3EvenBlock c.L n → PairWitness d c
  sp4 : ChapterC.IsSp4FourBlock c.L → PairWitness d c
  a6 : ChapterC.IsAlternatingBlock c.L 6 → PairWitness d c
  g2 : Nonempty (Chapter1.XiQuotient c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    PairWitness d c
  ahat6 : ChapterC.IsExceptionalAhat6Block c.L → PairWitness d c
  a7 : ChapterC.IsExceptionalA7Block c.L → PairWitness d c
  alternating : ∀ n, ChapterC.IsAlternatingBlock c.L n → PairWitness d c
  /-- The covering/model transport retained by 15.3.22 for the surviving
  `L₃(2)` case.  Its later normalizer exclusion belongs to 15.3.23. -/
  linearThree : ∀ _h : IsSLThreeEven (starImage c.L d.R c.L),
    ChapterC.IsLinearTwoBlock c.L 3 ∨ Nonempty (PairWitness d c)
  binaryLinear : ∀ n, n = 4 ∨ n = 5 →
    ClassicalGroup.IsPSL (starImage c.L d.R c.L) n 2 →
      ChapterC.IsLinearTwoBlock c.L n

theorem no_l2_block [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c) (n : ℕ)
    (h : ChapterC.IsL2EvenBlock c.L n) : False := pairWitness_false d c (e.l2 n h)

theorem no_sl3_block [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c) (n : ℕ)
    (hn : 1 < n) (h : ChapterC.IsSL3EvenBlock c.L n) : False :=
  pairWitness_false d c (e.sl3 n hn h)

theorem no_sp4_block [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c)
    (h : ChapterC.IsSp4FourBlock c.L) : False := pairWitness_false d c (e.sp4 h)

theorem no_alternating_block [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c) (n : ℕ)
    (h : ChapterC.IsAlternatingBlock c.L n) : False :=
  pairWitness_false d c (e.alternating n h)

/-! Named source eliminations.  The hypotheses are model records on the
actual carrier `L`; in particular, they do not assert that an arbitrary
quotient is a block. -/
theorem lemma_15_3_18 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c) {n : ℕ}
    (h : ChapterC.IsL2EvenBlock c.L n) : False :=
  no_l2_block d c e n h

theorem lemma_15_3_19 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c)
    (h : (∃ n, ChapterC.IsL2EvenBlock c.L n) ∨
      ChapterC.IsAlternatingBlock c.L 5) : False := by
  rcases h with ⟨n, hn⟩ | h5
  · exact lemma_15_3_18 d c e hn
  · exact no_alternating_block d c e 5 h5

theorem lemma_15_3_20 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c)
    {n : ℕ} (hn : 1 < n) (h : ChapterC.IsSL3EvenBlock c.L n) : False :=
  no_sl3_block d c e n hn h

theorem lemma_15_3_20_sp4 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c)
    (h : ChapterC.IsSp4FourBlock c.L) : False :=
  no_sp4_block d c e h

theorem lemma_15_3_21 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : ExclusionData d c)
    (h : ChapterC.IsAlternatingBlock c.L 6 ∨
      IsG2TwoBlock c.L ∨ ChapterC.IsExceptionalAhat6Block c.L ∨
      ChapterC.IsExceptionalA7Block c.L ∨ ChapterC.IsAlternatingBlock c.L 7) :
    False := by
  rcases h with h6 | hg2 | ha6 | ha7 | h7
  · exact no_alternating_block d c e 6 h6
  · exact pairWitness_false d c (e.g2 hg2.quotient_model)
  · exact pairWitness_false d c (e.ahat6 ha6)
  · exact pairWitness_false d c (e.a7 ha7)
  · exact no_alternating_block d c e 7 h7

/-! The actual model conclusion after the non-binary alternatives have been
removed.  The source list is first converted to its complete `ModelCases`
projection and only then is the exclusion data applied. -/
theorem lemma_15_3_22 [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (h : C27Data d c) (e : ExclusionData d c) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ ChapterC.IsLinearTwoBlock c.L n := by
  rcases (h.conclusion.alternatives.modelCases) with hm
  cases hm with
  | binary hb hm =>
      rcases hm with ⟨n, hn⟩
      exact (no_l2_block d c e n hn).elim
  | alternating n _ _ hb hm => exact (no_alternating_block d c e n hm).elim
  | ahatSix hm => exact (pairWitness_false d c (e.ahat6 hm)).elim
  | exceptionalSeven hm => exact (pairWitness_false d c (e.a7 hm)).elim
  | symplecticFour hm => exact (no_sp4_block d c e hm).elim
  | binaryG2 hm => exact (pairWitness_false d c (e.g2 hm)).elim
  | linearThree hm =>
      rcases e.linearThree hm with h3 | hw
      · exact ⟨3, ⟨Or.inl rfl, h3⟩⟩
      · exact (pairWitness_false d c hw.some).elim
  | binaryLinear n hn hm =>
      rcases hn with rfl | rfl
      · exact ⟨4, ⟨Or.inr (Or.inl rfl), e.binaryLinear 4 (Or.inl rfl) hm⟩⟩
      · exact ⟨5, ⟨Or.inr (Or.inr rfl), e.binaryLinear 5 (Or.inr rfl) hm⟩⟩

/-! The quotient part of 15.3.22 is exposed separately for consumers which
need the source's literal `L/O₂(L) ≅ Lₙ(2)` statement. -/
theorem lemma_15_3_22_quotient [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (h : C27Data d c) (e : ExclusionData d c) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) n 2 := by
  obtain ⟨n, hn, hm⟩ := lemma_15_3_22 d c h e
  exact ⟨n, hn, hm.2.2.1⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination

end
