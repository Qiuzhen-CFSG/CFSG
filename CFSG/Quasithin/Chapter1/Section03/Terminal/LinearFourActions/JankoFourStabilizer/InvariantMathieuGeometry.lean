module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction

/-!
# Invariant Mathieu overgroups for the J₄ L₄(2) sections

The checked reduction in `Reduction` constructs the actual quotient and its
Sylow-local image, and handles arbitrary isomorphic carriers. Final assembly
still requires `ConcreteInvariantMax1PlacementTheorem` and
`MathieuLocalFourExtensionTheorem`; no unconditional witness is asserted here.

Source: Aschbacher–Smith, A.3.12(14),(17), printed pp.47–48, and the proof
of 1.3.9, printed p.514. The two geometric assertions are separate from the
already proved M₂₄ stabilizer action calculation.
-/
