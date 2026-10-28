module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Hints
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# The literal X*Z = U prefix product

All 1242 rows are certified using the proved sequential XOR checker
and checked single-coordinate shortcuts, without transposition.
Each bounded proof checks at most twelve blocks of 27 rows.
Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2;
see `PrefixProducts/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

open PrefixProducts

set_option maxRecDepth 8192 in
private theorem u_part0 :
    check (Data.x00 ++ (Data.x01 ++ (Data.x02 ++ (Data.x03 ++ (Data.x04 ++ (Data.x05 ++ (Data.x06 ++ (Data.x07 ++ (Data.x08 ++ (Data.x09 ++ (Data.x10 ++ (Data.x11)))))))))))) Data.zRows (Data.u00 ++ (Data.u01 ++ (Data.u02 ++ (Data.u03 ++ (Data.u04 ++ (Data.u05 ++ (Data.u06 ++ (Data.u07 ++ (Data.u08 ++ (Data.u09 ++ (Data.u10 ++ (Data.u11)))))))))))) (xHints00 ++ (xHints01 ++ (xHints02 ++ (xHints03 ++ (xHints04 ++ (xHints05 ++ (xHints06 ++ (xHints07 ++ (xHints08 ++ (xHints09 ++ (xHints10 ++ (xHints11)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem u_part1 :
    check (Data.x12 ++ (Data.x13 ++ (Data.x14 ++ (Data.x15 ++ (Data.x16 ++ (Data.x17 ++ (Data.x18 ++ (Data.x19 ++ (Data.x20 ++ (Data.x21 ++ (Data.x22 ++ (Data.x23)))))))))))) Data.zRows (Data.u12 ++ (Data.u13 ++ (Data.u14 ++ (Data.u15 ++ (Data.u16 ++ (Data.u17 ++ (Data.u18 ++ (Data.u19 ++ (Data.u20 ++ (Data.u21 ++ (Data.u22 ++ (Data.u23)))))))))))) (xHints12 ++ (xHints13 ++ (xHints14 ++ (xHints15 ++ (xHints16 ++ (xHints17 ++ (xHints18 ++ (xHints19 ++ (xHints20 ++ (xHints21 ++ (xHints22 ++ (xHints23)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem u_part2 :
    check (Data.x24 ++ (Data.x25 ++ (Data.x26 ++ (Data.x27 ++ (Data.x28 ++ (Data.x29 ++ (Data.x30 ++ (Data.x31 ++ (Data.x32 ++ (Data.x33 ++ (Data.x34 ++ (Data.x35)))))))))))) Data.zRows (Data.u24 ++ (Data.u25 ++ (Data.u26 ++ (Data.u27 ++ (Data.u28 ++ (Data.u29 ++ (Data.u30 ++ (Data.u31 ++ (Data.u32 ++ (Data.u33 ++ (Data.u34 ++ (Data.u35)))))))))))) (xHints24 ++ (xHints25 ++ (xHints26 ++ (xHints27 ++ (xHints28 ++ (xHints29 ++ (xHints30 ++ (xHints31 ++ (xHints32 ++ (xHints33 ++ (xHints34 ++ (xHints35)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem u_part3 :
    check (Data.x36 ++ (Data.x37 ++ (Data.x38 ++ (Data.x39 ++ (Data.x40 ++ (Data.x41 ++ (Data.x42 ++ (Data.x43 ++ (Data.x44 ++ (Data.x45)))))))))) Data.zRows (Data.u36 ++ (Data.u37 ++ (Data.u38 ++ (Data.u39 ++ (Data.u40 ++ (Data.u41 ++ (Data.u42 ++ (Data.u43 ++ (Data.u44 ++ (Data.u45)))))))))) (xHints36 ++ (xHints37 ++ (xHints38 ++ (xHints39 ++ (xHints40 ++ (xHints41 ++ (xHints42 ++ (xHints43 ++ (xHints44 ++ (xHints45)))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

private theorem u_check : check Data.xRows Data.zRows Data.uRows xHints = true := by
  have h := check_append _ _ _ _ _ _ _ u_part0
    (check_append _ _ _ _ _ _ _ u_part1
      (check_append _ _ _ _ _ _ _ u_part2 u_part3))
  simpa only [Data.xRows, Data.uRows, xHints, List.append_assoc] using h

/-- The complete product on the published fixed matrices. -/
theorem u_product : Data.x * Data.z = Data.u := by
  exact product 1242 Data.xRows Data.zRows Data.uRows xHints
    Data.xRows_length Data.zRows_length u_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
