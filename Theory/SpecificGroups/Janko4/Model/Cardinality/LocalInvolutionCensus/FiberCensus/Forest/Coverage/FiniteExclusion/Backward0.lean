module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward0Part0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward0Part1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward0Part2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Backward0Part3

/-!
# Reverse row recurrence certificates for fiber 0

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem backward_checked0_12 (m : Fin 4096) :
    backwardTable0 (m.val + 4096) = backwardAction (backwardTable0 m.val) 12 := by
  apply check_blocks (P := fun a =>
    backwardTable0 (a + 4096) = backwardAction (backwardTable0 a) 12)
    (size := 2048) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked0_12_part0
  · exact backward_checked0_12_part1

theorem backward_steps0 (n : Fin 13) (m : Fin (2^n.val)) :
    backwardTable0 (m.val + 2^n.val) = backwardAction (backwardTable0 m.val) n := by
  fin_cases n
  · exact backward_checked0_0 m
  · exact backward_checked0_1 m
  · exact backward_checked0_2 m
  · exact backward_checked0_3 m
  · exact backward_checked0_4 m
  · exact backward_checked0_5 m
  · exact backward_checked0_6 m
  · exact backward_checked0_7 m
  · exact backward_checked0_8 m
  · exact backward_checked0_9 m
  · exact backward_checked0_10 m
  · exact backward_checked0_11 m
  · exact backward_checked0_12 m

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
