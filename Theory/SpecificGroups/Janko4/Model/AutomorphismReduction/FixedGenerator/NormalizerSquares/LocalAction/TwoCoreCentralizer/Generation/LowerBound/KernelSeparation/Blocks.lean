module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Rows
public import Mathlib.Tactic.FinCases

/-!
# Splitting finite certificates into blocks

Euclidean division combines bounded kernel checks without repeating
the entire finite quantifier in one reduction.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

theorem check_blocks {P : ℕ → Prop} {size blocks : ℕ} (hs : 0 < size)
    (h : ∀ b : Fin blocks, ∀ i : Fin size, P (size * b.val + i.val))
    (m : Fin (size * blocks)) : P m.val := by
  have hb : m.val / size < blocks := (Nat.div_lt_iff_lt_mul hs).2
    (by simpa only [Nat.mul_comm] using m.isLt)
  simpa only [Nat.div_add_mod] using
    h ⟨m.val / size, hb⟩ ⟨m.val % size, Nat.mod_lt _ hs⟩

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
