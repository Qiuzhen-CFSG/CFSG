module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward3Part0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward3Part1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward3Part2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Checks.Forward3Part3

/-!
# Forward row certificates for fiber 3

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

theorem forward_checked3 (m : Fin 8192) :
    forwardTable3 m.val = forwardAction (forwardTable0 m.val) 3 := by
  apply check_blocks (P := fun a => forwardTable3 a = forwardAction (forwardTable0 a) 3)
    (size := 2048) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact forward_checked3_part0
  · exact forward_checked3_part1
  · exact forward_checked3_part2
  · exact forward_checked3_part3

theorem forward_semantics3 (m : Fin 8192) :
    unpackRow (forwardTable3 m.val) = unpackRow (forwardRow 3 m) := by
  rw [forward_checked3, forward_checked0, forwardAction_eq]
  rfl

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
