module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.SeedFusion
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers
import Mathlib.Tactic.FinCases

/-!
# The small central-closure orders inside the literal Mathieu kernel

The full ambient centralizer of the 2B seed lies in literal max1. The two
checked local kernel orbits consequently show that every transporter of
that seed into the kernel lies in max1. A kernel subgroup containing a 2B
element therefore has normalizer in max1. Maximality would make it normal
in max1; the 1771-element pair orbit and the binary order bound exclude a
nontrivial elementary subgroup of order below 2048.

Thus the actual small closure contains no 2B element. The checked exhaustive
catalogue leaves six literal candidates, of orders 1, 2, 4, 8, 8 and 16.
Nontriviality excludes order one. The order-four candidate has its full ambient
normalizer strictly inside a proper conjugate of max4, contradicting maximality.
The order-sixteen candidate's full normalizer preserves the order-four candidate,
contradicting irreducibility. The surviving candidates have orders two and eight.

The final assembly discharges both concrete inputs and establishes
`smallKernelClosureOrders` without extra premises. This is exactly the kernel
branch consumed by `centralClosureOrderSpectrum_of_small_branches`; the outside
kernel branch remains with its independent owner.

Source: Aschbacher--Smith A.3.12, printed pp.47--48; Aschbacher (1986), no.343;
Kleidman--Wilson (1988), pp.484--510. The actual ATLAS matrices, local kernel,
and Sylow conventions are retained in the imports. Exploratory data in
`KernelOrders/source` supply no theorem or unchecked certificate.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Subgroup Janko4
open KernelOrders
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel

namespace KernelOrders

/-- Each allowed witness contradicts an actual fixed-Sylow closure premise. -/
theorem exceptional_candidate_not_fixed (hobs : ExceptionalNormalizerObstructions)
    (j : Fin 2) : ¬ FixedSylowClosure (candidate (exceptionalIndex j)) := by
  intro hA
  rcases hobs j with ⟨H, hlt, hproper⟩ | ⟨B, hBA, hB, hN⟩
  · exact hproper.ne (hA.maximal_normalizer.2 H hlt)
  · rcases hA.irreducible B hBA.le hN with h | h
    · exact hB h
    · exact hBA.ne h

end KernelOrders

/-- The small kernel branch, conditional only on the explicit all-2A catalogue
and the two exceptional full-normalizer calculations. -/
theorem smallKernelClosureOrders_of_pure_certificates
    (hcatalogue : PureKernelCatalogue) (hobs : ExceptionalNormalizerObstructions) :
    SmallKernelClosureOrders := by
  intro A hA hAK hsmall
  obtain ⟨i, rfl⟩ := hcatalogue.1 A hAK hA.sylow_normalizes
    (fixedSylowClosure_no_seed_conjugate A hA hAK hsmall)
  fin_cases i
  · exact (hA.nontrivial candidate_zero).elim
  · exact Or.inl (by simpa [candidateRows] using hcatalogue.2 1)
  · exact (exceptional_candidate_not_fixed hobs 0 hA).elim
  · exact Or.inr (by simpa [candidateRows] using hcatalogue.2 3)
  · exact Or.inr (by simpa [candidateRows] using hcatalogue.2 4)
  · exact (exceptional_candidate_not_fixed hobs 1 hA).elim

/-- Every small fixed-Sylow closure inside the literal Mathieu kernel has order
two or eight. The exhaustive catalogue and both full-normalizer obstructions
are discharged by the checked matrix and action calculations. -/
theorem smallKernelClosureOrders : SmallKernelClosureOrders :=
  smallKernelClosureOrders_of_pure_certificates
    pureKernelCatalogue exceptionalNormalizerObstructions

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
