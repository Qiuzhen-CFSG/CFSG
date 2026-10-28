module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Homology
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer

/-!
# The full homology kernel has order at most 8192

For v = (a - 1)e₀, the full kernel orbit is covered by the specified 4096
vectors, and its point stabilizer is contained in {1,a}. The independently
proved `OrbitCover` and `VectorStabilizer` certificates apply to all actual
model elements in the homology kernel. Orbit–stabilizer therefore gives
the unconditional bound 8192.

Source motivation: GLS3, Table 5.3i, printed p.270. Its asserted centralizer
structure is not used as a premise, nor is full generation by the max2 words.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

/-- Count all kernel elements from a covering of the vector orbit and a bound
on its point stabilizer. The unconditional theorem below supplies both
universal premises. -/
theorem homologyAction_kernel_card_le_of_vector_certificates
    (hcover : ∀ c : homologyAction.ker, ∃ m : KernelBound.OrbitMask,
      naturalAction (c : involutionCentralizer)
        (KernelBound.baseVector : NaturalModule) = KernelBound.representativeVector m)
    (hfix : ∀ c : homologyAction.ker,
      naturalAction (c : involutionCentralizer)
        (KernelBound.baseVector : NaturalModule) = KernelBound.baseVector →
        (c : involutionCentralizer) = 1 ∨ (c : involutionCentralizer) = centralInvolution) :
    Nat.card homologyAction.ker ≤ 8192 := by
  rw [KernelBound.card_kernel_eq_orbit_mul_stabilizer]
  exact Nat.mul_le_mul (KernelBound.vectorOrbit_card_le_of_cover hcover)
    (KernelBound.vectorStabilizer_card_le_of_fixers hfix)

/-- The kernel of the entire literal centralizer's action on
`ker(a - 1) / im(a - 1)` has at most 8192 elements. -/
theorem homologyAction_kernel_card_le : Nat.card homologyAction.ker ≤ 8192 :=
  homologyAction_kernel_card_le_of_vector_certificates
    KernelBound.vector_orbit_cover KernelBound.vector_stabilizer_eq_one_or_involution

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
