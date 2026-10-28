module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries

/-!
# Original 13.6.2 after the nonabelian A₅ classification

The order-two Sylow-invariant source line puts its full centralizer in the
original H_z family as soon as that centralizer escapes N_G(L). The proved
normal and nonnormal A₅ recognition then discharge the 13.5.12 implication
used by the abelian-span argument. The actual V-span under C_G(z) is abelian,
and the original chosen module lies in O₂(C_G(z)).

The last two conclusions supply the literal abelian-closure field of
EarlierA5Setup and the source two-core placement used by the centralizer
argument. Only the genuine earlier A.3.12 input, original marked Context,
centralizer escape and the two actual model exclusions remain.
Source: Aschbacher–Smith 13.5.12 and 13.6.1–2, printed pp.918 and926.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.SourceAbelian
open CentralizerReduction TerminalContradiction.Ratio Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
include d

omit [IsElementaryAbelian 2 V] in
/-- The full source point centralizer belongs to H_z; family membership is
constructed from the invariant line and the original escape condition. -/
theorem point_centralizer_mem_family
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G)) :
    centralizer (V₁ : Set G) ∈ Section08.Source.Hz (residualCentralizer L V₁)
      (T : Subgroup G) (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
  have hTZ : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  have hlineT : V₁ ≤ (T : Subgroup G) :=
    d.flag.one_le_two.trans (d.flag.two_le_V.trans d.chosen.le_sylow)
  have hc : V₁ ≤ (centralizer (V₁ : Set G)).pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hlineT) (hlineT.trans hTZ) (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨?_,sup_le (map_subtype_le _ |>.trans inf_le_right) hTZ⟩,le_rfl,houtside⟩
  intro he
  have hb := bot_unique (hc.trans_eq he)
  have hcard := d.flag.one_card
  rw [hb,card_bot] at hcard
  contradiction

include hA312

/-- The actual A₅ specialization of 13.5.12, in the form used by 13.6.2. -/
theorem source_nonabelian_classification
    (hH : H ∈ Section08.Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ H)) :
    ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3 := by
  have h := source_modelConclusion (D := ⟨T,L,V,V₃,V₁,H⟩) d hA312 hH hU
  rcases h with h | h
  · exact h.2
  · exact (by omega : False).elim

/-- Original 13.6.2 for the full point centralizer and every local subgroup,
with both 13.5.10 and the nonabelian classification discharged. -/
theorem source_13_6_2 (z : G)
    (hz : zpowers z = V₁)
    (houtside : ¬ Gv z ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    IsMulCommutative (conjugateSpanBy V (Gv z)) ∧
      ∀ H : Subgroup G, H ≤ Gv z → IsMulCommutative (conjugateSpanBy V H) := by
  have hc : centralizer (V₁ : Set G) = Gv z := by
    rw [←hz, zpowers_eq_closure, centralizer_closure]
    rfl
  have hH : Gv z ∈ Section08.Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
    rw [←hc]
    exact point_centralizer_mem_family d (hc.symm ▸ houtside)
  exact abelian_spans_of_earlier_source V V₃ z hcounter
    (source_nonabelian_classification d hA312 hH)
    (source13_5_10 d hA312 hH).1.1

/-- The literal abelian-closure field used in the terminal A₅ source setup. -/
theorem source_closure_abelian (z : G)
    (hz : zpowers z = V₁)
    (houtside : ¬ Gv z ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    IsMulCommutative (centralizerConjugateClosure V z) := by
  rw [centralizerConjugateClosure_eq_conjugateSpanBy]
  exact (source_13_6_2 d hA312 z hz houtside hcounter).1

/-- The original chosen module lies in the actual point-centralizer two-core. -/
theorem source_le_point_core (z : G)
    (hz : zpowers z = V₁)
    (houtside : ¬ Gv z ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) : V ≤ (Gv z).pCoreIn 2 := by
  have hc : centralizer (V₁ : Set G) = Gv z := by
    rw [←hz, zpowers_eq_closure, centralizer_closure]
    rfl
  have hH : Gv z ∈ Section08.Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
    rw [←hc]
    exact point_centralizer_mem_family d (hc.symm ▸ houtside)
  exact (closure_abelian_iff_le_core d z (source13_5_7 d hA312 hH)).mp
    (source_closure_abelian d hA312 z hz houtside hcounter)
end CFSG.Quasithin.Chapter13.Section06.SourceAbelian
