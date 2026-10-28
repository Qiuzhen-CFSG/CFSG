module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Certificate

/-!
# Packed row checks for both native forward maps

Each bounded certificate transforms six packed masks, sorts them, and compares
with the saved target row. The bit-network semantics in `Certificate` turn
these integer identities into the native finset action. All 1771 rows for both
generators are checked by the kernel; the data are never trusted externally.

Sources and conventions: `Degrees120252/Native252/source/README.md` and
`Degrees120252/source/README.md`; James (1973), GM02 Proposition 5.1.
-/

-- Bounded certificates were measured before expansion. Sequential elaboration
-- avoids retaining many independent kernel computations at once.
set_option Elab.async false

@[expose] public section
open scoped Pointwise
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Certificate

def lookup (n : ℕ) : List ℕ := (pointMasks[n % 1771]?).getD []

set_option maxRecDepth 4096 in
private theorem forward0_chunk0 :
    pointMasksChunk0.map (transform 0) = forwardRows0Chunk0.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk1 :
    pointMasksChunk1.map (transform 0) = forwardRows0Chunk1.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk2 :
    pointMasksChunk2.map (transform 0) = forwardRows0Chunk2.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk3 :
    pointMasksChunk3.map (transform 0) = forwardRows0Chunk3.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk4 :
    pointMasksChunk4.map (transform 0) = forwardRows0Chunk4.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk5 :
    pointMasksChunk5.map (transform 0) = forwardRows0Chunk5.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk6 :
    pointMasksChunk6.map (transform 0) = forwardRows0Chunk6.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk7 :
    pointMasksChunk7.map (transform 0) = forwardRows0Chunk7.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk8 :
    pointMasksChunk8.map (transform 0) = forwardRows0Chunk8.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk9 :
    pointMasksChunk9.map (transform 0) = forwardRows0Chunk9.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk10 :
    pointMasksChunk10.map (transform 0) = forwardRows0Chunk10.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk11 :
    pointMasksChunk11.map (transform 0) = forwardRows0Chunk11.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk12 :
    pointMasksChunk12.map (transform 0) = forwardRows0Chunk12.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk13 :
    pointMasksChunk13.map (transform 0) = forwardRows0Chunk13.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk14 :
    pointMasksChunk14.map (transform 0) = forwardRows0Chunk14.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk15 :
    pointMasksChunk15.map (transform 0) = forwardRows0Chunk15.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk16 :
    pointMasksChunk16.map (transform 0) = forwardRows0Chunk16.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk17 :
    pointMasksChunk17.map (transform 0) = forwardRows0Chunk17.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk18 :
    pointMasksChunk18.map (transform 0) = forwardRows0Chunk18.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk19 :
    pointMasksChunk19.map (transform 0) = forwardRows0Chunk19.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk20 :
    pointMasksChunk20.map (transform 0) = forwardRows0Chunk20.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk21 :
    pointMasksChunk21.map (transform 0) = forwardRows0Chunk21.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk22 :
    pointMasksChunk22.map (transform 0) = forwardRows0Chunk22.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk23 :
    pointMasksChunk23.map (transform 0) = forwardRows0Chunk23.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk24 :
    pointMasksChunk24.map (transform 0) = forwardRows0Chunk24.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk25 :
    pointMasksChunk25.map (transform 0) = forwardRows0Chunk25.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk26 :
    pointMasksChunk26.map (transform 0) = forwardRows0Chunk26.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward0_chunk27 :
    pointMasksChunk27.map (transform 0) = forwardRows0Chunk27.map lookup := by
  decide +kernel

private theorem forward0_rows :
    pointMasks.map (transform 0) = forwardRows0.map lookup := by
  simp only [pointMasks, forwardRows0, List.map_flatten, List.map_cons, List.map_nil,
    forward0_chunk0, forward0_chunk1, forward0_chunk2, forward0_chunk3, forward0_chunk4, forward0_chunk5, forward0_chunk6, forward0_chunk7, forward0_chunk8, forward0_chunk9, forward0_chunk10, forward0_chunk11, forward0_chunk12, forward0_chunk13, forward0_chunk14, forward0_chunk15, forward0_chunk16, forward0_chunk17, forward0_chunk18, forward0_chunk19, forward0_chunk20, forward0_chunk21, forward0_chunk22, forward0_chunk23, forward0_chunk24, forward0_chunk25, forward0_chunk26, forward0_chunk27]

set_option maxRecDepth 4096 in
private theorem forward1_chunk0 :
    pointMasksChunk0.map (transform 1) = forwardRows1Chunk0.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk1 :
    pointMasksChunk1.map (transform 1) = forwardRows1Chunk1.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk2 :
    pointMasksChunk2.map (transform 1) = forwardRows1Chunk2.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk3 :
    pointMasksChunk3.map (transform 1) = forwardRows1Chunk3.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk4 :
    pointMasksChunk4.map (transform 1) = forwardRows1Chunk4.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk5 :
    pointMasksChunk5.map (transform 1) = forwardRows1Chunk5.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk6 :
    pointMasksChunk6.map (transform 1) = forwardRows1Chunk6.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk7 :
    pointMasksChunk7.map (transform 1) = forwardRows1Chunk7.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk8 :
    pointMasksChunk8.map (transform 1) = forwardRows1Chunk8.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk9 :
    pointMasksChunk9.map (transform 1) = forwardRows1Chunk9.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk10 :
    pointMasksChunk10.map (transform 1) = forwardRows1Chunk10.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk11 :
    pointMasksChunk11.map (transform 1) = forwardRows1Chunk11.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk12 :
    pointMasksChunk12.map (transform 1) = forwardRows1Chunk12.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk13 :
    pointMasksChunk13.map (transform 1) = forwardRows1Chunk13.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk14 :
    pointMasksChunk14.map (transform 1) = forwardRows1Chunk14.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk15 :
    pointMasksChunk15.map (transform 1) = forwardRows1Chunk15.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk16 :
    pointMasksChunk16.map (transform 1) = forwardRows1Chunk16.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk17 :
    pointMasksChunk17.map (transform 1) = forwardRows1Chunk17.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk18 :
    pointMasksChunk18.map (transform 1) = forwardRows1Chunk18.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk19 :
    pointMasksChunk19.map (transform 1) = forwardRows1Chunk19.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk20 :
    pointMasksChunk20.map (transform 1) = forwardRows1Chunk20.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk21 :
    pointMasksChunk21.map (transform 1) = forwardRows1Chunk21.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk22 :
    pointMasksChunk22.map (transform 1) = forwardRows1Chunk22.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk23 :
    pointMasksChunk23.map (transform 1) = forwardRows1Chunk23.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk24 :
    pointMasksChunk24.map (transform 1) = forwardRows1Chunk24.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk25 :
    pointMasksChunk25.map (transform 1) = forwardRows1Chunk25.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk26 :
    pointMasksChunk26.map (transform 1) = forwardRows1Chunk26.map lookup := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem forward1_chunk27 :
    pointMasksChunk27.map (transform 1) = forwardRows1Chunk27.map lookup := by
  decide +kernel

private theorem forward1_rows :
    pointMasks.map (transform 1) = forwardRows1.map lookup := by
  simp only [pointMasks, forwardRows1, List.map_flatten, List.map_cons, List.map_nil,
    forward1_chunk0, forward1_chunk1, forward1_chunk2, forward1_chunk3, forward1_chunk4, forward1_chunk5, forward1_chunk6, forward1_chunk7, forward1_chunk8, forward1_chunk9, forward1_chunk10, forward1_chunk11, forward1_chunk12, forward1_chunk13, forward1_chunk14, forward1_chunk15, forward1_chunk16, forward1_chunk17, forward1_chunk18, forward1_chunk19, forward1_chunk20, forward1_chunk21, forward1_chunk22, forward1_chunk23, forward1_chunk24, forward1_chunk25, forward1_chunk26, forward1_chunk27]

set_option maxRecDepth 4096 in
theorem lengths : pointMasks.map List.length = List.replicate 1771 6 := by
  decide +kernel

/-- Both complete forward tables, in the original saved row order. -/
theorem rows_forward (j : Fin 2) :
    pointMasks.map (transform j) = (![forwardRows0, forwardRows1] j).map lookup := by
  fin_cases j
  · exact forward0_rows
  · exact forward1_rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Certificate
