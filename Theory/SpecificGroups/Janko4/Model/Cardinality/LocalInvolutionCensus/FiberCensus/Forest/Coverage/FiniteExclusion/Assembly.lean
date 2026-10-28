module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Witnesses

/-!
# From checked row tables to published mask witnesses

The recurrence theorem identifies the inverse-word rows, and bounded packed
rows are determined by their 112 decoded bits. The finite table certificate
then supplies an index into an unchanged public mask list.
Source: ATLAS J4G1-max2W1; see `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem covered_of_tables (j : Fin 4) (f b : ℕ → ℕ)
    (hf : ∀ m : Fin 8192, unpackRow (f m.val) = unpackRow (forwardRow j m))
    (hz : b 0 = liftEntry j 0)
    (hs : ∀ (n : Fin 13) (m : Fin (2^n.val)),
      b (m.val + 2^n.val) = backwardAction (b m.val) n)
    (hfb : ∀ m : Fin 8192, f m.val < 2^112)
    (hbb : ∀ m : Fin 8192, b m.val < 2^112)
    (hc : ∀ m : Fin 8192, f m.val = b (reverseCode m).val → Listed j m.val)
    (m : Fin 8192) (h : RowsAgree j m) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k := by
  apply listed_covered j m
  apply hc m
  apply unpackRow_inj (hfb m) (hbb (reverseCode m))
  have hzero : b 0 = (liftRows j).get 0 := hz.trans (liftEntry_checked j 0)
  have hstep : ∀ (n : Fin 13) (a : Fin (2^n.val)),
      b (a.val + 2^n.val) = packedRow (b a.val) (inverseFactorRows ⟨12-n.val, by omega⟩) := by
    intro n a
    rw [hs, backwardAction_eq]
  rw [hf]
  exact h.trans (table_backward b j hzero hstep m)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
