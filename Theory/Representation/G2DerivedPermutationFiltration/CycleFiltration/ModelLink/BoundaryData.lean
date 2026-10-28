module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CosetAction
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates
/-!
# Matching the two cycle certificate tables

The numerical boundary is the pair of endpoint pushforwards in the certified
literal coset enumeration. Entries of its two blocks are checked in the kernel.
These identities support the actual cycle-kernel coordinates used for
Aschbacher–Smith G.7.2(3), printed pp.347–348 / PDF pp.358–359.
-/

@[expose] public section

open scoped BigOperators
open Representation
open G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.CycleData
open G2DerivedPermutationFiltration.CycleData.Certificate
open G2DerivedPermutationFiltration.CycleFlagCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates
namespace G2DerivedPermutationFiltration.CycleModelLink
lemma endpoint_eq : ∀ (i : Fin 2) (x : Fin 189),
    CycleFlagCoordinates.endpoint i x = Certificate.endpoint i x := by intros; rfl

lemma pushEval (i : Fin 2) (f : Fin 189 → ZMod 2) (r : Fin 63) :
    (pushForward i (flagCoordinates.symm f)) (vertex i r) =
      ∑ x : Fin 189, f x * (if CycleFlagCoordinates.endpoint i x = r then 1 else 0) := by
  rw [pushForward_coordinates]
  simp [vertexBasis, Pi.single_apply, (vertex_injective i).eq_iff, endpoint_eq, eq_comm]

lemma boundary_entry0 : ∀ (r : Fin 63) (x : Fin 189),
    boundaryMatrix (Fin.castAdd 63 r) x = if Certificate.endpoint 0 x = r then 1 else 0 := by decide +kernel

lemma boundary_entry1 : ∀ (r : Fin 63) (x : Fin 189),
    boundaryMatrix (Fin.natAdd 63 r) x = if Certificate.endpoint 1 x = r then 1 else 0 := by decide +kernel

lemma boundaryRow0 (f : Fin 189 → ZMod 2) (r : Fin 63) :
    (boundaryMatrix.mulVec f) (Fin.castAdd 63 r) =
      ∑ x : Fin 189, f x * (if Certificate.endpoint 0 x = r then 1 else 0) := by
  rw [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro x hx
  change boundaryMatrix (Fin.castAdd 63 r) x * f x = _
  rw [show boundaryMatrix (Fin.castAdd 63 r) x = if Certificate.endpoint 0 x = r then 1 else 0 from boundary_entry0 r x]
  by_cases h : Certificate.endpoint 0 x = r <;> simp [h]

lemma boundaryRow1 (f : Fin 189 → ZMod 2) (r : Fin 63) :
    (boundaryMatrix.mulVec f) (Fin.natAdd 63 r) =
      ∑ x : Fin 189, f x * (if Certificate.endpoint 1 x = r then 1 else 0) := by
  rw [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro x hx
  change boundaryMatrix (Fin.natAdd 63 r) x * f x = _
  rw [show boundaryMatrix (Fin.natAdd 63 r) x = if Certificate.endpoint 1 x = r then 1 else 0 from boundary_entry1 r x]
  by_cases h : Certificate.endpoint 1 x = r <;> simp [h]
end G2DerivedPermutationFiltration.CycleModelLink
