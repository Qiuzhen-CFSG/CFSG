module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward2Part0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward2Part1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward2Part2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward2Part3

/-!
# Reverse row recurrence certificates for fiber 2

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem backward_checked2_12 (m : Fin 4096) :
    backwardTable2 (m.val + 4096) = backwardAction (backwardTable2 m.val) 12 := by
  apply check_blocks (P := fun a =>
    backwardTable2 (a + 4096) = backwardAction (backwardTable2 a) 12)
    (size := 2048) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_12_part0
  · exact backward_checked2_12_part1

theorem backward_steps2 (n : Fin 13) (m : Fin (2^n.val)) :
    backwardTable2 (m.val + 2^n.val) = backwardAction (backwardTable2 m.val) n := by
  fin_cases n
  · exact backward_checked2_0 m
  · exact backward_checked2_1 m
  · exact backward_checked2_2 m
  · exact backward_checked2_3 m
  · exact backward_checked2_4 m
  · exact backward_checked2_5 m
  · exact backward_checked2_6 m
  · exact backward_checked2_7 m
  · exact backward_checked2_8 m
  · exact backward_checked2_9 m
  · exact backward_checked2_10 m
  · exact backward_checked2_11 m
  · exact backward_checked2_12 m

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
