module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.RecognitionKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.Complete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries

/-!
# The original A₅ point-centralizer closure over known simple groups

The callback-free nonabelian recognition and seed geometry discharge both
inputs of 13.6.2. The full point-centralizer closure is abelian, as is every
local subclosure, and the chosen module lies in the literal two-core. These
are the original closure premises of the terminal A₅ parameter setup.

Source: Aschbacher–Smith 13.5.12 and 13.6.1–2, printed pp.918,926.
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
include d

/-- The actual A₅ specialization of 13.5.12, in the form used by 13.6.2. -/
theorem source_nonabelian_classification_knownSimple
    (hH : H ∈ Section08.Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ H)) :
    ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3 := by
  have h := source_modelConclusion_knownSimple d hH hU
  rcases h with h | h
  · exact h.2
  · exact (by omega : False).elim

/-- Original 13.6.2 for the full point centralizer and every local subgroup,
with both 13.5.10 and the nonabelian classification discharged. -/
theorem source_13_6_2_knownSimple (z : G)
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
    (source_nonabelian_classification_knownSimple d hH)
    (source13_5_10_knownSimple d hH).1.1

/-- The literal abelian-closure field used in the terminal A₅ source setup. -/
theorem source_closure_abelian_knownSimple (z : G)
    (hz : zpowers z = V₁)
    (houtside : ¬ Gv z ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    IsMulCommutative (centralizerConjugateClosure V z) := by
  rw [centralizerConjugateClosure_eq_conjugateSpanBy]
  exact (source_13_6_2_knownSimple d z hz houtside hcounter).1

/-- The original chosen module lies in the actual point-centralizer two-core. -/
theorem source_le_point_core_knownSimple (z : G)
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
  exact (closure_abelian_iff_le_core d z (source13_5_7_knownSimple d hH)).mp
    (source_closure_abelian_knownSimple d z hz houtside hcounter)
end CFSG.Quasithin.Chapter13.Section06.SourceAbelian
