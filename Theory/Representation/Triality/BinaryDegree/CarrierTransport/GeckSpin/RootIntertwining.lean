module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining.Actions
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin

/-!
# Both signed Geck simple roots act by Clifford conjugation

The full 28-coordinate comparison sends root vectors to the pinned Clifford
bivectors and Cartan vectors to the corresponding Clifford commutators.
The eight basis calculations agree with the literal integral Geck divided
powers. Linearity proves compatibility on every vector, for both signs,
with central vertex 1, arms 0, 2, 3, and the unchanged parameter.

No injectivity or faithfulness hypothesis is used in these identities.
The final application discharges the two root-action premises of the finite
comparison constructor; its independent injectivity and separation premises
remain explicit.

Source: GLS3, §§1.12–1.14, especially the adjoint module in 1.14.9(c),
and §2.7 (`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open RootPairing.SimpleGeckGroup

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Positive simple-root conjugation agrees with the literal Geck action on all coordinates. -/
theorem positive_intertwines (i : Fin 4) (t : k) :
    Intertwines k (positive (typeDRootPairing_baseEquiv 2 i) t)
      (positiveSimplePoint k i t) :=
  RootIntertwining.signed_intertwines k true i t

/-- Negative simple-root conjugation agrees with the literal Geck action on all coordinates. -/
theorem negative_intertwines (i : Fin 4) (t : k) :
    Intertwines k (negative (typeDRootPairing_baseEquiv 2 i) t)
      (negativeSimplePoint k i t) :=
  RootIntertwining.signed_intertwines k false i t

/-- The two signed root-action premises of the finite comparison are discharged.
Only the independent embedding and Spin-separation obligations remain. -/
theorem exists_finite_comparison_of_clifford_separation
    (hι : Function.Injective (embedding k))
    (hfaith : ∀ x y : Points k,
      (∀ v, pointConjugation k x (embedding k v) =
        pointConjugation k y (embedding k v)) → x = y)
    {n : ℕ} {hpos : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hpos) →+* k) :
    ∃ e : Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hpos) →* Points k,
      Function.Injective e ∧ HasRootFormula f e :=
  exists_finite_comparison_of_clifford k hι hfaith
    (positive_intertwines k) (negative_intertwines k) f

end Triality.BinaryDegree.CarrierTransport.GeckSpin
