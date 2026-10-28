module

public import Stellmacher.Recognition.OddCoreCompletion
public import BenderSuzuki.SE.SimpleOddCore

/-!
# Excluding a strongly embedded completed-core normalizer

In a finite simple N2 group, the normalizer of the actual involution
odd-core closure of an elementary abelian two-subgroup of order at least
eight is not strongly embedded. Signalizer completion makes this closure
an odd-order subgroup. The Bender–Suzuki odd-core theorem then excludes
strong embedding of its normalizer.

This is the strong-embedding elimination in the global odd-core argument
of GLS2, Section 21.8, using Bender–Suzuki Theorem SE and the completion
theorem of Kurzweil–Stellmacher, Theorem 11.2.9. It does not require a
connectivity hypothesis or assert unconditional vanishing of the closure.
-/

namespace Stellmacher.Recognition

/-- The completed involution odd-core closure in a finite simple N2 group
cannot have a strongly embedded normalizer. -/
public theorem not_isStronglyEmbedded_normalizer_involutionOddCoreClosure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) :
    ¬ IsStronglyEmbedded
      (Subgroup.normalizer (involutionOddCoreClosure A : Set G)) := by
  intro hM
  have hMB : BenderSuzuki.IsStronglyEmbedded
      (Subgroup.normalizer (involutionOddCoreClosure A : Set G)) := by
    let M := Subgroup.normalizer (involutionOddCoreClosure A : Set G)
    refine ⟨hM.1, hM.2.1, ?_⟩
    intro g hg x hxM hxright
    have hginv : g⁻¹ ∉ M := fun hi => hg (by simpa using M.inv_mem hi)
    apply hM.2.2 g⁻¹ hginv x
    refine ⟨hxM, ?_⟩
    simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hxright
  exact BenderSuzuki.not_isStronglyEmbedded_normalizer_of_odd
    (involutionOddCoreClosure A) (involutionOddCoreClosure_complete hN A hA).1 hMB

end Stellmacher.Recognition
