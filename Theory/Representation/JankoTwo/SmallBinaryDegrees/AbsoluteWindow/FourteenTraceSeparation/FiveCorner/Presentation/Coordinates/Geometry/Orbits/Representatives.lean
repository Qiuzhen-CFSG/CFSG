module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.Lookup

/-!
# The saved representative words reach the fixed roots

The compact evaluator is proved equal to the literal walk. The checks below
retain the original representativeWord decoder, so no parent-order assumption
or replacement list of words enters the certificate.

Source: Presentation/source/discovery/coset-parents.json and orbits.json;
Coordinates/source/generate_data.py fixes the retained decoding.
-/

set_option Elab.async false

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

set_option maxRecDepth 4096 in
private theorem chunk0 : checkRange representativeCheck 0 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk1 : checkRange representativeCheck 64 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk2 : checkRange representativeCheck 128 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk3 : checkRange representativeCheck 192 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk4 : checkRange representativeCheck 256 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk5 : checkRange representativeCheck 320 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk6 : checkRange representativeCheck 384 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk7 : checkRange representativeCheck 448 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk8 : checkRange representativeCheck 512 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk9 : checkRange representativeCheck 576 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk10 : checkRange representativeCheck 640 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk11 : checkRange representativeCheck 704 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk12 : checkRange representativeCheck 768 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk13 : checkRange representativeCheck 832 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk14 : checkRange representativeCheck 896 64 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem chunk15 : checkRange representativeCheck 960 48 = true := by
  decide +kernel

private theorem representativeChecks : checkRange representativeCheck 0 1008 = true :=
  (checkRange_append (start := 0) (n := 960) (m := 48) (checkRange_append (start := 0) (n := 896) (m := 64) (checkRange_append (start := 0) (n := 832) (m := 64) (checkRange_append (start := 0) (n := 768) (m := 64) (checkRange_append (start := 0) (n := 704) (m := 64) (checkRange_append (start := 0) (n := 640) (m := 64) (checkRange_append (start := 0) (n := 576) (m := 64) (checkRange_append (start := 0) (n := 512) (m := 64) (checkRange_append (start := 0) (n := 448) (m := 64) (checkRange_append (start := 0) (n := 384) (m := 64) (checkRange_append (start := 0) (n := 320) (m := 64) (checkRange_append (start := 0) (n := 256) (m := 64) (checkRange_append (start := 0) (n := 192) (m := 64) (checkRange_append (start := 0) (n := 128) (m := 64) (checkRange_append (start := 0) (n := 64) (m := 64) chunk0 chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14) chunk15)


theorem representatives
    (i : Fin 1008) : walk (representativeWord i) 0 = root i := by
  have hi : (⟨i.val % 1008, Nat.mod_lt _ (by decide)⟩ : Fin 1008) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have h := checkRange_sound representativeChecks (j := i.val) (by omega) (by omega)
  simp only [representativeCheck, hi, fastRoot_eq, beq_iff_eq] at h
  apply Fin.ext
  exact (run_eq_walk (representativeWord i) 0).symm.trans h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits
