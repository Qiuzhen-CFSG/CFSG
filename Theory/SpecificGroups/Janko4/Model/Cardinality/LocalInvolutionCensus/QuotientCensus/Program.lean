module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch6
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramChecks.Batch7
import Mathlib.Tactic.FinCases

/-!
# Checked membership of every quotient-census word

Every edge in the multiplication program is checked by packed binary matrix
arithmetic. Strong induction supplies actual Q elements with those matrices.
No ambient matrix-group membership oracle or order assertion is used.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound QuotientOrderCertificate

theorem program_checked (i : Fin 7392) : programCheck i := by
  have h (b : Fin 58) (r : Fin 128) :
      programCheck (Fin.ofNat 7392 (128 * b.val + r.val)) := by
    fin_cases b
    · exact ProgramChecks.block0 r
    · exact ProgramChecks.block1 r
    · exact ProgramChecks.block2 r
    · exact ProgramChecks.block3 r
    · exact ProgramChecks.block4 r
    · exact ProgramChecks.block5 r
    · exact ProgramChecks.block6 r
    · exact ProgramChecks.block7 r
    · exact ProgramChecks.block8 r
    · exact ProgramChecks.block9 r
    · exact ProgramChecks.block10 r
    · exact ProgramChecks.block11 r
    · exact ProgramChecks.block12 r
    · exact ProgramChecks.block13 r
    · exact ProgramChecks.block14 r
    · exact ProgramChecks.block15 r
    · exact ProgramChecks.block16 r
    · exact ProgramChecks.block17 r
    · exact ProgramChecks.block18 r
    · exact ProgramChecks.block19 r
    · exact ProgramChecks.block20 r
    · exact ProgramChecks.block21 r
    · exact ProgramChecks.block22 r
    · exact ProgramChecks.block23 r
    · exact ProgramChecks.block24 r
    · exact ProgramChecks.block25 r
    · exact ProgramChecks.block26 r
    · exact ProgramChecks.block27 r
    · exact ProgramChecks.block28 r
    · exact ProgramChecks.block29 r
    · exact ProgramChecks.block30 r
    · exact ProgramChecks.block31 r
    · exact ProgramChecks.block32 r
    · exact ProgramChecks.block33 r
    · exact ProgramChecks.block34 r
    · exact ProgramChecks.block35 r
    · exact ProgramChecks.block36 r
    · exact ProgramChecks.block37 r
    · exact ProgramChecks.block38 r
    · exact ProgramChecks.block39 r
    · exact ProgramChecks.block40 r
    · exact ProgramChecks.block41 r
    · exact ProgramChecks.block42 r
    · exact ProgramChecks.block43 r
    · exact ProgramChecks.block44 r
    · exact ProgramChecks.block45 r
    · exact ProgramChecks.block46 r
    · exact ProgramChecks.block47 r
    · exact ProgramChecks.block48 r
    · exact ProgramChecks.block49 r
    · exact ProgramChecks.block50 r
    · exact ProgramChecks.block51 r
    · exact ProgramChecks.block52 r
    · exact ProgramChecks.block53 r
    · exact ProgramChecks.block54 r
    · exact ProgramChecks.block55 r
    · exact ProgramChecks.block56 r
    · exact ProgramChecks.block57 r
  have hi := h ⟨i.val / 128, by omega⟩ ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : 128 * (i.val / 128) + i.val % 128 = i.val := by omega
  simpa only [he, Fin.ofNat_val_eq_self] using hi

theorem code_realized (i : Fin 7392) : ∃ g : Q, g.val.val = decode (code i) := by
  apply program_membership code left right
  · intro i hi
    simpa only [programCheck, if_pos hi] using program_checked i
  · intro i hi
    have hn : ¬ i.val < 4 := by omega
    have hh := program_checked i
    simp only [programCheck, hn] at hh
    exact ⟨hh.1, hh.2.1⟩
  · intro i hi
    have hn : ¬ i.val < 4 := by omega
    have hh := program_checked i
    simp only [programCheck, hn] at hh
    exact hh.2.2

noncomputable def element (i : Fin 7392) : Q := (code_realized i).choose

theorem element_val (i : Fin 7392) : (element i).val.val = decode (code i) :=
  (code_realized i).choose_spec

theorem element_mul (i : Fin 7392) (hi : 4 ≤ i.val) :
    element (left i) * element (right i) = element i := by
  apply Subtype.ext
  apply Units.ext
  change (element (left i)).val.val * (element (right i)).val.val = (element i).val.val
  rw [element_val, element_val, element_val]
  have hh := program_checked i
  have hn : ¬ i.val < 4 := by omega
  simp only [programCheck, hn] at hh
  exact mulCheck_sound hh.2.2

/-- Reuse a checked program edge when available, and check the product otherwise. -/
abbrev productCheck (i j k : Fin 7392) : Prop :=
  (4 ≤ k.val ∧ left k = i ∧ right k = j) ∨ mulCheck (code i) (code j) (code k)

theorem productCheck_sound {i j k : Fin 7392} (h : productCheck i j k) :
    element i * element j = element k := by
  rcases h with ⟨hk, hi, hj⟩ | h
  · simpa only [hi, hj] using element_mul k hk
  · apply Subtype.ext
    apply Units.ext
    change (element i).val.val * (element j).val.val = (element k).val.val
    rw [element_val, element_val, element_val]
    exact mulCheck_sound h

theorem element_zero : element 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [element_val]
  decide +kernel

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
