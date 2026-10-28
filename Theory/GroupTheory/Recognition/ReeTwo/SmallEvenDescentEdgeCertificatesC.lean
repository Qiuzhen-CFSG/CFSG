module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificateChecks

/-!
# Encoded word equations for small even descent edges 1900 through 2799

The fixed witnesses are checked in batches of fifty by kernel reduction.
The last batch wraps within this slice when necessary. The bounded index
calculation below covers every original edge in the slice.

Source: Shinoda (1975), (2.3), pp. 81–82, and the witness provenance in
`SmallEvenDescentEdgeData` and `SmallEvenDescentEdgeWords`.
-/

namespace ReeTwo.SylowModel.SmallEvenDescentEdges.Certificates

private def sliceIndex (b : Fin 18) (j : Fin 50) : Fin 3617 :=
  ⟨1900 + (b.val * 50 + j.val) % 900, by
    have := Nat.mod_lt (b.val * 50 + j.val) (by decide : 0 < 900)
    omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked0 : ∀ j, EncodedValid (sliceIndex 0 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked1 : ∀ j, EncodedValid (sliceIndex 1 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked2 : ∀ j, EncodedValid (sliceIndex 2 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked3 : ∀ j, EncodedValid (sliceIndex 3 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked4 : ∀ j, EncodedValid (sliceIndex 4 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked5 : ∀ j, EncodedValid (sliceIndex 5 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked6 : ∀ j, EncodedValid (sliceIndex 6 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked7 : ∀ j, EncodedValid (sliceIndex 7 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked8 : ∀ j, EncodedValid (sliceIndex 8 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked9 : ∀ j, EncodedValid (sliceIndex 9 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked10 : ∀ j, EncodedValid (sliceIndex 10 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked11 : ∀ j, EncodedValid (sliceIndex 11 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked12 : ∀ j, EncodedValid (sliceIndex 12 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked13 : ∀ j, EncodedValid (sliceIndex 13 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked14 : ∀ j, EncodedValid (sliceIndex 14 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked15 : ∀ j, EncodedValid (sliceIndex 15 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked16 : ∀ j, EncodedValid (sliceIndex 16 j) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked17 : ∀ j, EncodedValid (sliceIndex 17 j) := by decide +kernel

private theorem checked (b : Fin 18) : ∀ j, EncodedValid (sliceIndex b j) := by
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17

/-- All original edge rows in the indicated interval satisfy the encoded equations. -/
public theorem encoded_valid_C (e : Fin 3617) (hlo : 1900 ≤ e.val) (hhi : e.val < 2800) :
    EncodedValid e := by
  let b : Fin 18 := ⟨(e.val - 1900) / 50, by omega⟩
  let j : Fin 50 := ⟨(e.val - 1900) % 50, Nat.mod_lt _ (by decide)⟩
  have he : sliceIndex b j = e := by
    apply Fin.ext
    dsimp [sliceIndex, b, j]
    omega
  have h := checked b j
  simpa only [he] using h

end ReeTwo.SylowModel.SmallEvenDescentEdges.Certificates
