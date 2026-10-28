module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness.Coordinates
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness.Points
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin

/-!
# Separation for the literal Geck-to-Spin comparison

The Fock coefficient calculations prove injectivity of the full 28-coordinate
Clifford embedding. Root generation and natural irreducibility show that Spin
conjugation on its image separates points. These discharge precisely `hι` and
`hfaith` in the finite comparison theorem. The remaining signed root-action
identities are the independent intertwining input, retained by final assembly.

Source: GLS3, §§1.12–1.14, especially 1.14.9(c), and §2.7
(`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`).
-/

public section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open RootPairing.SimpleGeckGroup
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The concrete separation results discharge both faithfulness premises of the
finite comparison, for every positive binary exponent. -/
theorem exists_finite_comparison_of_signed_intertwining
    (hp : ∀ i t, Intertwines k
      (positive (typeDRootPairing_baseEquiv 2 i) t) (positiveSimplePoint k i t))
    (hn : ∀ i t, Intertwines k
      (negative (typeDRootPairing_baseEquiv 2 i) t) (negativeSimplePoint k i t))
    {n : ℕ} {hpos : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hpos) →+* k) :
    ∃ e : Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hpos) →* Points k,
      Function.Injective e ∧ HasRootFormula f e :=
  exists_finite_comparison_of_clifford k (embedding_injective k)
    (pointConjugation_ext k) hp hn f

end Triality.BinaryDegree.CarrierTransport.GeckSpin
