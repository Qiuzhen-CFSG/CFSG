module

public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
# Uniqueness from Dynkin type

This module identifies finite reduced crystallographic real root pairings that
carry the same `RootClassification`.  The `HasDynkinType` witnesses provide a
numbered base for each pairing whose integral Cartan matrix is the standard
Dynkin matrix.  Transporting one numbering through the other therefore makes
the two base Cartan matrices equal, and
`RootPairing.Base.equivOfCartanMatrixEq` extends that equality to an
equivalence of the full root pairings.

The principal theorem is the reusable classification bridge from concrete
Dynkin-type witnesses to root-pairing isomorphisms.  It formalizes the standard
uniqueness of a finite reduced root system from its based Cartan matrix, using
the Dynkin tables in `Theory.AlgebraicGroup.RootSystems.Dynkin` and Mathlib's
root-system uniqueness theorem.
-/

universe u

namespace Theory.AlgebraicGroup

/-- Finite reduced crystallographic real root pairings with the same Dynkin
classification are isomorphic. -/
public theorem rootPairing_isomorphic_of_hasDynkinType
    {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι' ℝ F F') [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (classification : RootClassification)
    (hP : HasDynkinType P classification)
    (hQ : HasDynkinType Q classification) :
    P.IsIsomorphic Q := by
  obtain ⟨bP, eP, hP⟩ := hP
  obtain ⟨bQ, eQ, hQ⟩ := hQ
  let e : bP.support ≃ bQ.support := eP.trans eQ.symm
  refine ⟨bP.equivOfCartanMatrixEq bQ e ?_⟩
  intro i j
  change bQ.cartanMatrixIn ℤ (e i) (e j) =
    bP.cartanMatrixIn ℤ i j
  rw [hQ, hP]
  simp [e]

end Theory.AlgebraicGroup
