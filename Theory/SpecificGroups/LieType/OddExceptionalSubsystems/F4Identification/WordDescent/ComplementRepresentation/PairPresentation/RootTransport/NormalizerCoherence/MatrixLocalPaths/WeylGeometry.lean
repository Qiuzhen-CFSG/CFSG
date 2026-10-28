module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths.WeylGeometry.Certificates

/-!
# Signed-simple two-node factorization in the actual F4 Weyl group

This proves the geometric contract consumed by `lift_weyl_path` and the
matrix-normalizer path assembly. A finite Schreier transversal gives a root
state for every word. Each simple-reflection edge has a certified correction
made of standard two-node paths, including its full root-stabilizer action.
Induction composes those corrections in the original multiplication order.
At a signed-simple endpoint the representative is empty, so the accumulated
path represents the specified Weyl element itself.

The integer checks are connected to the existing real F4 root pairing by its
simple-root basis. Every intermediate mark is explicitly a signed numbered
simple root. This supplies an F4 proof of the factorization consequence of
GLS3 Lemma 2.9.4 (`refs/KGroup/GLS3/chapter2.tex`, lines 1399–1427).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
namespace WeylGeometry
/-- Schreier reduction keeps the entire Weyl element as a product of a root
representative and a path between signed simple roots. -/
lemma word_reduction (w : List Node) (x : Mark) :
    ∃ r : Fin 48, WeylPairPath
      ((numberedProd (routeWord r))⁻¹ * typeF4RootPairing_base.wordProd w)
      x (routeMark r) := by
  induction w with
  | nil =>
    refine ⟨markState x, ?_⟩
    rw [routeWord_markState, numberedProd_nil, inv_one,
      RootPairing.Base.wordProd_nil, one_mul, routeMark_markState]
    exact WeylPairPath.refl x
  | cons q w ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective q
    refine ⟨nextState r i, ?_⟩
    have hp := hr.trans (edge r i)
    have he :
        ((numberedProd (routeWord (nextState r i)))⁻¹ *
          typeF4RootPairing_base.simpleReflection (sourceIndex i) *
          numberedProd (routeWord r)) *
          ((numberedProd (routeWord r))⁻¹ * typeF4RootPairing_base.wordProd w) =
        (numberedProd (routeWord (nextState r i)))⁻¹ *
          typeF4RootPairing_base.wordProd (sourceIndex i :: w) := by
      rw [RootPairing.Base.wordProd_cons]
      group
    rw [he] at hp
    exact hp

end WeylGeometry

/-- The actual F4 Weyl group satisfies the signed-simple two-node
factorization of GLS3 Lemma 2.9.4. The equality retains the original Weyl
element, including its action on the stabilizer of the marked root. -/
theorem hasWeylPairPaths : HasWeylPairPaths := by
  intro w s z i j hw
  obtain ⟨r, hr⟩ := WeylGeometry.word_reduction w (s, i)
  have he : typeF4RootPairing.weylGroupToPerm
      (WeylGeometry.numberedProd (WeylGeometry.routeWord r))
      (signedRoot (WeylGeometry.routeMark r).1 (WeylGeometry.routeMark r).2) =
      signedRoot z j := by
    rw [← hr.endpoint]
    change typeF4RootPairing.weylGroupToPerm
      (WeylGeometry.numberedProd (WeylGeometry.routeWord r) *
        ((WeylGeometry.numberedProd (WeylGeometry.routeWord r))⁻¹ *
          typeF4RootPairing_base.wordProd w)) (signedRoot s i) = signedRoot z j
    simpa only [mul_inv_cancel_left] using hw
  have hc := (WeylGeometry.numberedProd_endpoint_iff
    (WeylGeometry.routeWord r) (WeylGeometry.routeMark r) (z, j)).mp he
  obtain ⟨hword, hmark⟩ := WeylGeometry.route_terminal r (z, j) hc
  simpa only [hword, WeylGeometry.numberedProd_nil, inv_one, one_mul, hmark] using hr

/-- Discharge the geometric premise of the literal matrix-path assembly.
The curve-transport and Tits-square identities are the two independent inputs
still belonging to their matrix-theoretic producers. -/
theorem hasNormalizerTransportPaths_of_transport_and_squares
    (F : Type*) [Field F] [Finite F]
    (hc : SimpleTransport F) (ht : HasSquareCorrections F) :
    HasNormalizerTransportPaths F :=
  hasNormalizerTransportPaths_of_inputs F hasWeylPairPaths hc ht

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
