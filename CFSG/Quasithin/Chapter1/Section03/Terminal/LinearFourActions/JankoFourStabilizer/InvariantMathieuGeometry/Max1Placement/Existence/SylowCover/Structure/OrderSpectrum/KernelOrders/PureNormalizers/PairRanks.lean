module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.RankReduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PairRanks.Bounds

/-!
# The intrinsic pair-rank distinction in the literal kernel sixteen-group

The actual mask enumeration is proved from the XOR group law, independently
of the all-2A catalogue. Twenty-five checked matrix products evaluate the
sixteen words. Nineteen rectangular factorizations prove the small upper
bounds, while seven independent seventeen-row minors supply the separating
witnesses. All arithmetic is checked by the kernel, with no native evaluation.

The final corollary applies the rank criterion to the FULL ambient normalizer,
as required by the second exceptional branch of Aschbacher–Smith A.3.12,
printed pp.47–48; see also Kleidman–Wilson (1988), pp.484–510. Original
ATLAS attribution and the binary bit convention are in Janko4.Model.Data
and KernelCount.Tables. The reproducible witness generator is in
PairRanks/source/generate.py; its calculations are not trusted as proofs.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Subgroup Janko4
open PairRanks
attribute [local irreducible] modelGroup matrixA matrixB

/-- Precisely the literal four-group has all pair ranks at most sixteen. -/
theorem smallPairRanks : SmallPairRanks := by
  intro u hu
  rw [candidate_five_eq_sixteenRange] at hu
  obtain ⟨i, rfl⟩ := hu
  constructor
  · intro h
    rcases finite_dichotomy i with ⟨k, hk⟩ | ⟨j, hj⟩
    · rw [candidate_two_eq_fourRange]
      exact ⟨k, congrArg maskElement hk.symm⟩
    · have hv : maskElement (sixteenMask j) ∈ candidate 5 := by
        rw [candidate_five_eq_sixteenRange]
        exact ⟨j, rfl⟩
      exact False.elim (not_lt_of_ge (h _ hv) hj)
  · intro hu2 v hv
    rw [candidate_two_eq_fourRange] at hu2
    obtain ⟨k, hk⟩ := hu2
    rw [candidate_five_eq_sixteenRange] at hv
    obtain ⟨j, rfl⟩ := hv
    rw [← hk]
    exact upper k j

/-- The certified rank criterion supplies a proper nonzero subgroup preserved
by every element of the full ambient normalizer of the sixteen-group. -/
theorem candidate_five_obstruction :
    ∃ B : Subgroup Model, B < candidate (exceptionalIndex 1) ∧ B ≠ ⊥ ∧
      normalizer (candidate (exceptionalIndex 1) : Set Model) ≤
        normalizer (B : Set Model) :=
  candidate_five_obstruction_of_pair_ranks smallPairRanks

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
