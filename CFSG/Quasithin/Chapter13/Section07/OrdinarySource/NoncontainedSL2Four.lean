module
public import CFSG.Quasithin.Chapter13.Section07.L1ChiefCount
public import CFSG.Quasithin.Chapter13.Section07.PairOffenderIndices
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# The chief-count contradiction in original 13.7.19

The original two-conjugate actor is nontrivial. The exact 13.7.10(8) count
therefore gives at least three noncentral binary chief factors in every
complete series of the literal point residual. This replaces the separate
scalar and diagonal chief-count calculations at the end of 13.7.19.

The block consumer retains the precise earlier-source input: an A₆ block
bounds the literal point residual by two noncentral binary chief factors.
Constructing that block from the noncontained natural SL₂(4) component is
a separate normalizer-escape argument; no containment premise is used here.
Source: Aschbacher–Smith, 13.7.10(8), 13.7.12(3), and 13.7.19, printed
pp.941–942 and 945.
-/

public section
open Subgroup NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original pair forces at least three noncentral binary factors. -/
theorem source_L1_chief_count_ge_three
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : t.head = ⊥) (h1 : t.last = ⊤) : 3 ≤ t.noncentralTwoCount := by
  let Astar := ((conjugate (Section08.Source.VH H V) (g : G) ⊓
    (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H))
  have hn : Astar ≠ ⊥ := (pair_actor_elementary_nontrivial d h hU hV g hs hout).2.2
  have hc : 1 < Nat.card Astar := (one_lt_card_iff_ne_bot Astar).mpr hn
  have hl := Nat.log_mono_right (b := 2) (show 2 ≤ Nat.card Astar by omega)
  rw [show Nat.log 2 2 = 1 from by decide] at hl
  have ht := source_L1_full_chief_count d h hU hV g hs hspan hout t h0 h1
  change t.noncentralTwoCount = Nat.log 2 (Nat.card Astar) + 2 at ht
  omega

/-- The complete literal point residual cannot have a two-factor bound. -/
theorem source_L1_false_of_two_chief_bound
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hbound : ∀ t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁,
      t.head = ⊥ → t.last = ⊤ → t.noncentralTwoCount ≤ 2) : False := by
  obtain ⟨g,hs,hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g : G) hspan hU hV
  obtain ⟨t,h0,h1⟩ := exists_chiefSeries
    (⊥ : NormalNode (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁) ⊤ bot_le
  have hl := source_L1_chief_count_ge_three d h hU hV
    (inclusion le_sup_left g) hs hspan hout t h0 h1
  have hu := hbound t h0 h1
  omega

/-- The end of 13.7.19, retaining the actual block-to-point-residual input. -/
theorem source_not_alternatingBlock_of_chief_bound
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hblockCount : ChapterC.IsAlternatingBlock
      (L.subgroupOf (L ⊔ (T : Subgroup G) : Subgroup G)) 6 →
      ∀ t : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁,
        t.head = ⊥ → t.last = ⊤ → t.noncentralTwoCount ≤ 2) :
    ¬ ChapterC.IsAlternatingBlock
      (L.subgroupOf (L ⊔ (T : Subgroup G) : Subgroup G)) 6 := by
  intro hb
  exact source_L1_false_of_two_chief_bound d h hU hV (hblockCount hb)

end CFSG.Quasithin.Chapter13.Section07
