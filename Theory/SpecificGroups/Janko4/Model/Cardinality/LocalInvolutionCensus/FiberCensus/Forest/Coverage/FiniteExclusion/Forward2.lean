module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward2Part0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward2Part1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward2Part2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward2Part3

/-!
# Forward row certificates for fiber 2

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem forward_checked2 (m : Fin 8192) :
    forwardTable2 m.val = forwardAction (forwardTable0 m.val) 2 := by
  apply check_blocks (P := fun a => forwardTable2 a = forwardAction (forwardTable0 a) 2)
    (size := 2048) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact forward_checked2_part0
  · exact forward_checked2_part1
  · exact forward_checked2_part2
  · exact forward_checked2_part3

theorem forward_semantics2 (m : Fin 8192) :
    unpackRow (forwardTable2 m.val) = unpackRow (forwardRow 2 m) := by
  rw [forward_checked2, forward_checked0, forwardAction_eq]
  rfl

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
