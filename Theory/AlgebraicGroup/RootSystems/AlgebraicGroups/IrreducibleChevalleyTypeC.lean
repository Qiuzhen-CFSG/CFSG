module

public import Theory.AlgebraicGroup.RootSystems.SymplecticProjectiveRootModel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemModelTransport

/-!
# Irreducible type-C Chevalley carriers

An irreducible reduced crystallographic real root pairing whose based Cartan
matrix is the type `C_{m+1}` path matrix is equivalent to the standard
coordinate type-C pairing.  Composing this equivalence with the universe-lift
equivalence transports two explicit semisimple models back to the given
pairing: the standard symplectic carrier and its actual finite-center
projective quotient.

The imported symplectic modules construct the maximal diagonal tori, classify
all their torus roots, assemble exhaustive actual based root realizations, and
prove semisimplicity in every characteristic.  This module only performs the
final root-pairing transport.  The Cartan classification is GLS, Part I,
Theorem 1.8.7, while the concrete carriers follow the standard type-C models
used in Sections 1.9--1.10.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A based irreducible type-C root pairing has both its standard symplectic
and projective symplectic semisimple versions. -/
public theorem typeC_chevalleyRootModelPair_exists
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) (m : ℕ) (e : Fin (m + 1) ≃ b.support)
    (he : ∀ i j,
      b.cartanMatrix (e i) (e j) = typeCCartanMatrix m i j) :
    Nonempty
      (SemisimpleVersion (k := k) P × SemisimpleVersion (k := k) P) := by
  obtain ⟨hP⟩ := typeC_rootPairing_equiv b m e he
  let hLift : P.Equiv (typeCRootPairingULift (m + 1)) :=
    RootPairing.Equiv.comp
      (RootPairing.Equiv.symm _ _
        (typeCRootPairingULiftEquiv (m + 1))) hP
  obtain ⟨projectiveVersion⟩ :=
    exists_standard_projective_symplectic_version (k := k) (m + 1)
  exact ⟨
    SemisimpleVersion.transport hLift
      (standardSymplecticCarrierVersion (k := k) (m + 1)),
    SemisimpleVersion.transport hLift projectiveVersion⟩

end Theory.AlgebraicGroup
