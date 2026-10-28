module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Hints
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# The literal X*Y = Z prefix product

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
private theorem z_part0 :
    check (Data.x00 ++ (Data.x01 ++ (Data.x02 ++ (Data.x03 ++ (Data.x04 ++ (Data.x05 ++ (Data.x06 ++ (Data.x07 ++ (Data.x08 ++ (Data.x09 ++ (Data.x10 ++ (Data.x11)))))))))))) Data.yRows (Data.z00 ++ (Data.z01 ++ (Data.z02 ++ (Data.z03 ++ (Data.z04 ++ (Data.z05 ++ (Data.z06 ++ (Data.z07 ++ (Data.z08 ++ (Data.z09 ++ (Data.z10 ++ (Data.z11)))))))))))) (xHints00 ++ (xHints01 ++ (xHints02 ++ (xHints03 ++ (xHints04 ++ (xHints05 ++ (xHints06 ++ (xHints07 ++ (xHints08 ++ (xHints09 ++ (xHints10 ++ (xHints11)))))))))))) = true := by
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
private theorem z_part1 :
    check (Data.x12 ++ (Data.x13 ++ (Data.x14 ++ (Data.x15 ++ (Data.x16 ++ (Data.x17 ++ (Data.x18 ++ (Data.x19 ++ (Data.x20 ++ (Data.x21 ++ (Data.x22 ++ (Data.x23)))))))))))) Data.yRows (Data.z12 ++ (Data.z13 ++ (Data.z14 ++ (Data.z15 ++ (Data.z16 ++ (Data.z17 ++ (Data.z18 ++ (Data.z19 ++ (Data.z20 ++ (Data.z21 ++ (Data.z22 ++ (Data.z23)))))))))))) (xHints12 ++ (xHints13 ++ (xHints14 ++ (xHints15 ++ (xHints16 ++ (xHints17 ++ (xHints18 ++ (xHints19 ++ (xHints20 ++ (xHints21 ++ (xHints22 ++ (xHints23)))))))))))) = true := by
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
private theorem z_part2 :
    check (Data.x24 ++ (Data.x25 ++ (Data.x26 ++ (Data.x27 ++ (Data.x28 ++ (Data.x29 ++ (Data.x30 ++ (Data.x31 ++ (Data.x32 ++ (Data.x33 ++ (Data.x34 ++ (Data.x35)))))))))))) Data.yRows (Data.z24 ++ (Data.z25 ++ (Data.z26 ++ (Data.z27 ++ (Data.z28 ++ (Data.z29 ++ (Data.z30 ++ (Data.z31 ++ (Data.z32 ++ (Data.z33 ++ (Data.z34 ++ (Data.z35)))))))))))) (xHints24 ++ (xHints25 ++ (xHints26 ++ (xHints27 ++ (xHints28 ++ (xHints29 ++ (xHints30 ++ (xHints31 ++ (xHints32 ++ (xHints33 ++ (xHints34 ++ (xHints35)))))))))))) = true := by
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
private theorem z_part3 :
    check (Data.x36 ++ (Data.x37 ++ (Data.x38 ++ (Data.x39 ++ (Data.x40 ++ (Data.x41 ++ (Data.x42 ++ (Data.x43 ++ (Data.x44 ++ (Data.x45)))))))))) Data.yRows (Data.z36 ++ (Data.z37 ++ (Data.z38 ++ (Data.z39 ++ (Data.z40 ++ (Data.z41 ++ (Data.z42 ++ (Data.z43 ++ (Data.z44 ++ (Data.z45)))))))))) (xHints36 ++ (xHints37 ++ (xHints38 ++ (xHints39 ++ (xHints40 ++ (xHints41 ++ (xHints42 ++ (xHints43 ++ (xHints44 ++ (xHints45)))))))))) = true := by
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

private theorem z_check : check Data.xRows Data.yRows Data.zRows xHints = true := by
  have h := check_append _ _ _ _ _ _ _ z_part0
    (check_append _ _ _ _ _ _ _ z_part1
      (check_append _ _ _ _ _ _ _ z_part2 z_part3))
  simpa only [Data.xRows, Data.zRows, xHints, List.append_assoc] using h

/-- The complete product on the published fixed matrices. -/
theorem z_product : Data.x * Data.y = Data.z := by
  exact product 1242 Data.xRows Data.yRows Data.zRows xHints
    Data.xRows_length Data.yRows_length z_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
