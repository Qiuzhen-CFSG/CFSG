module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CosetAction.Bytes

/-!
# Checked geometric images of the 189 G₂ flags

Each inverse representative word sends the standard incident line–point pair
to the endpoint pair in the saved flag ordering. The pairs are distinct.
The eight ambient letters and the two inverse derived words send each pair
to exactly the destination recorded by the literal permutation tables.
The finite byte and permutation identities are all kernel checked; Bytes
transports the byte identities to the actual octonion action.

Witness provenance and ATLAS attribution are in Data and source/README.md.
Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
open scoped Pointwise
namespace G2DerivedPermutationFiltration.CycleFlagCoordinates
open VertexCoordinates VertexCoordinates.ActionGeometry
set_option maxRecDepth 16000

def flagImage (x : Fin 189) : Fin 2 → Finset (Carrier (ZMod 2)) :=
  fun i => image i (endpoint i x)

private theorem representativeWord_signed : ∀ x a, a ∈ representativeWord x →
    a.2 = 1 ∨ a.2 = -1 := by
  intro x
  have h : ∀ x, (representativeWord x).all (fun a => decide (a.2 = 1 ∨ a.2 = -1)) := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h x

private theorem generatorWord_signed : ∀ x a, a ∈ generatorWord x →
    a.2 = 1 ∨ a.2 = -1 := by
  intro x
  have h : ∀ x, (generatorWord x).all (fun a => decide (a.2 = 1 ∨ a.2 = -1)) := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h x

set_option maxHeartbeats 2000000 in
private theorem packed_representative_images : ∀ (x : Fin 189) (i : Fin 2),
    (if i = 0 then ({1,2,3} : Finset (Fin 256)) else {1}).image
      (inverseBytes (representativeWord x)) = imageTable i (endpoint i x) := by
  decide +kernel

theorem representative_images (x : Fin 189) (i : Fin 2) :
    (evalWord (representativeWord x))⁻¹ • base i = flagImage x i := by
  unfold base flagImage image
  rw [inverseBytes_finset _ (representativeWord_signed x), packed_representative_images]

private def endpointLookup (p q : Fin 63) : Fin 189 :=
  if endpoint 1 (endpointFiber p 0) = q then endpointFiber p 0
  else if endpoint 1 (endpointFiber p 1) = q then endpointFiber p 1
  else endpointFiber p 2

private theorem endpointLookup_endpoint : ∀ x,
    endpointLookup (endpoint 0 x) (endpoint 1 x) = x := by
  decide +kernel

theorem endpoints_injective : Function.Injective (fun x => (endpoint 0 x, endpoint 1 x)) := by
  intro x y h
  have hh := congrArg (fun p : Fin 63 × Fin 63 => endpointLookup p.1 p.2) h
  simpa only [endpointLookup_endpoint] using hh

set_option maxHeartbeats 2000000 in
private theorem packed_ambient_images : ∀ (j : Fin 8) (x : Fin 189) (i : Fin 2),
    (imageTable i (endpoint i x)).image (rootByte j) =
      imageTable i (endpoint i (ambientTable j x)) := by
  decide +kernel

theorem ambient_images (j : Fin 8) (x : Fin 189) (i : Fin 2) :
    rootGenerator j • flagImage x i = flagImage (ambientTable j x) i := by
  unfold flagImage image
  rw [rootByte_finset, packed_ambient_images]

set_option maxHeartbeats 2000000 in
private theorem packed_derived_images : ∀ (j : Fin 2) (x : Fin 189) (i : Fin 2),
    (imageTable i (endpoint i x)).image (inverseBytes (generatorWord j)) =
      imageTable i (endpoint i (derivedTable j x)) := by
  decide +kernel

theorem derived_images (j : Fin 2) (x : Fin 189) (i : Fin 2) :
    ambientGenerator j • flagImage x i = flagImage (derivedTable j x) i := by
  unfold ambientGenerator flagImage image
  rw [inverseBytes_finset _ (generatorWord_signed j), packed_derived_images]

theorem ambientTable_involutive : ∀ (j : Fin 8), Function.Involutive (ambientTable j) := by
  change ∀ (j : Fin 8) (x : Fin 189), ambientTable j (ambientTable j x) = x
  decide +kernel

theorem derivedTable_left : ∀ j x, derivedInverseTable j (derivedTable j x) = x := by
  decide +kernel

theorem derivedTable_right : ∀ j x, derivedTable j (derivedInverseTable j x) = x := by
  decide +kernel

end G2DerivedPermutationFiltration.CycleFlagCoordinates
