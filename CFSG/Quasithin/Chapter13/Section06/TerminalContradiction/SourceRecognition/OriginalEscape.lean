module
public import Mathlib.Tactic.Linter.FlexibleLinter
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCatalogue
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.Transport
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import Theory.Representation.BinaryPermutation.FiveAction

/-!
# The original A5 orbit escape adapter

The source 12.2.13 alternatives are stated for a nonzero vector in the
original elementary module.  The A5 marking has exactly the two nonzero
orbits represented by the singular and nonsingular markings.  This file
transports the resulting escaping vector to the marked line centralizer,
which is the `houtside` premise used by the terminal catalogue.

The orbit transport is the source-level bridge; no model classification is
hidden in this adapter.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
theorem marking_nonzero_two_orbits (s : Marking L V) {x : G}
    (hx : x ∈ V) (hx1 : x ≠ 1) :
    (∃ l ∈ L, MulAut.conj l x = markedZ s) ∨
    (∃ l ∈ L, MulAut.conj l x = markedV s) := by
  obtain ⟨w, rfl⟩ := s.range_eq.ge hx
  have hw : w.toAdd ≠ 0 := by
    intro h
    apply hx1
    have hw1 : w = 1 := congrArg Multiplicative.ofAdd h
    rw [hw1, map_one]
  by_cases hq : FiveGeometry.form w.toAdd = 0
  · obtain ⟨a, ha⟩ := FiveGeometry.exists_even_transport w.toAdd z hw z_ne_zero
      (hq.trans (by decide : FiveGeometry.form z = 0).symm)
    obtain ⟨l, hl⟩ := s.onto a
    refine Or.inl ⟨l, l.property, ?_⟩
    change MulAut.conj (l : G) (s.map (Multiplicative.ofAdd w.toAdd)) = _
    rw [s.equivariant, hl, ha]
    rfl
  · have hq1 : FiveGeometry.form w.toAdd = 1 :=
      (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hq
    obtain ⟨a, ha⟩ := FiveGeometry.exists_even_transport w.toAdd v hw v_ne_zero
      (hq1.trans (by decide : FiveGeometry.form v = 1).symm)
    obtain ⟨l, hl⟩ := s.onto a
    refine Or.inr ⟨l, l.property, ?_⟩
    change MulAut.conj (l : G) (s.map (Multiplicative.ofAdd w.toAdd)) = _
    rw [s.equivariant, hl, ha]
    rfl

theorem singular_escape_of_vector_escape
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (hex : ∃ x ∈ V, x ≠ 1 ∧ ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G) := by
  intro hline
  obtain ⟨x, hx, hx1, hxC⟩ := hex
  rcases marking_nonzero_two_orbits d.flag.flag.module hx hx1 with
    ⟨l, hl, he⟩ | ⟨l, hl, he⟩
  · apply hxC
    apply Chapter12.Section06.CentralLine.centralizer_le_of_conjugate (L.le_normalizer hl)
    rw [he]
    have hsame : centralizer ({markedZ d.flag.flag.module} : Set G) = centralizer (V₁ : Set G) := by
      calc
        centralizer ({markedZ d.flag.flag.module} : Set G) =
            centralizer (Subgroup.closure ({markedZ d.flag.flag.module} : Set G) : Set G) := by
          rw [Subgroup.centralizer_closure]
        _ = centralizer (V₁ : Set G) :=
          congrArg (fun A : Subgroup G => centralizer (A : Set G)) <|
            (Subgroup.zpowers_eq_closure (markedZ d.flag.flag.module)).symm.trans
              d.flag.flag.line_eq
    exact hsame.symm ▸ hline
  · apply hxC
    apply Chapter12.Section06.CentralLine.centralizer_le_of_conjugate (L.le_normalizer hl)
    rw [he]
    exact hCv.trans d.module_normalizer

theorem original_hypothesis1223 (d : Context T L V V₁ V₂ V₃) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L := by
  exact { Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient with
    no_rankTwo := d.hypothesis.hypothesis1311.no_rankTwo
    no_M22 := d.hypothesis.hypothesis1311.no_M22
    no_M23 := d.hypothesis.hypothesis1311.no_M23
    no_J4 := d.hypothesis.hypothesis1311.no_J4 }

theorem vector_escape_of_source12213 (d : Context T L V V₁ V₂ V₃)
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple) :
    ∃ x ∈ V, x ≠ 1 ∧ ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  rcases h12213 G T L V (original_hypothesis1223 d) d.chosen with hx | hl | ha | hm
  · exact hx
  · obtain ⟨n, hn, _, hg⟩ := hl
    exact (d.hypothesis.no_linear (n+1) (by rcases hn with rfl | rfl <;> simp) hg).elim
  · exact (d.hypothesis.no_alternating_nine ha.2).elim
  · exact (d.hypothesis.hypothesis1311.no_M24 hm.2).elim

theorem source_qtkeModel_of_A5_context_of_source12213
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple)
    (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u}
      KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  exact source_qtkeModel_of_A5_context d hCv
    (singular_escape_of_vector_escape d hCv (vector_escape_of_source12213 d h12213)) h523

theorem false_of_original_A5_context_of_source12213
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple)
    (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hnot : ¬ ClassificationModels.IsQTKEModel G) : False :=
  hnot (source_qtkeModel_of_A5_context_of_source12213 d hCv h12213 h523)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
