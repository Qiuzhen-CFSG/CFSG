module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Hints
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# The literal X*B = Y prefix product

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
private theorem y_part0 :
    check (Data.x00 ++ (Data.x01 ++ (Data.x02 ++ (Data.x03 ++ (Data.x04 ++ (Data.x05 ++ (Data.x06 ++ (Data.x07 ++ (Data.x08 ++ (Data.x09 ++ (Data.x10 ++ (Data.x11)))))))))))) Data.bRows (Data.y00 ++ (Data.y01 ++ (Data.y02 ++ (Data.y03 ++ (Data.y04 ++ (Data.y05 ++ (Data.y06 ++ (Data.y07 ++ (Data.y08 ++ (Data.y09 ++ (Data.y10 ++ (Data.y11)))))))))))) (xHints00 ++ (xHints01 ++ (xHints02 ++ (xHints03 ++ (xHints04 ++ (xHints05 ++ (xHints06 ++ (xHints07 ++ (xHints08 ++ (xHints09 ++ (xHints10 ++ (xHints11)))))))))))) = true := by
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
private theorem y_part1 :
    check (Data.x12 ++ (Data.x13 ++ (Data.x14 ++ (Data.x15 ++ (Data.x16 ++ (Data.x17 ++ (Data.x18 ++ (Data.x19 ++ (Data.x20 ++ (Data.x21 ++ (Data.x22 ++ (Data.x23)))))))))))) Data.bRows (Data.y12 ++ (Data.y13 ++ (Data.y14 ++ (Data.y15 ++ (Data.y16 ++ (Data.y17 ++ (Data.y18 ++ (Data.y19 ++ (Data.y20 ++ (Data.y21 ++ (Data.y22 ++ (Data.y23)))))))))))) (xHints12 ++ (xHints13 ++ (xHints14 ++ (xHints15 ++ (xHints16 ++ (xHints17 ++ (xHints18 ++ (xHints19 ++ (xHints20 ++ (xHints21 ++ (xHints22 ++ (xHints23)))))))))))) = true := by
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
private theorem y_part2 :
    check (Data.x24 ++ (Data.x25 ++ (Data.x26 ++ (Data.x27 ++ (Data.x28 ++ (Data.x29 ++ (Data.x30 ++ (Data.x31 ++ (Data.x32 ++ (Data.x33 ++ (Data.x34 ++ (Data.x35)))))))))))) Data.bRows (Data.y24 ++ (Data.y25 ++ (Data.y26 ++ (Data.y27 ++ (Data.y28 ++ (Data.y29 ++ (Data.y30 ++ (Data.y31 ++ (Data.y32 ++ (Data.y33 ++ (Data.y34 ++ (Data.y35)))))))))))) (xHints24 ++ (xHints25 ++ (xHints26 ++ (xHints27 ++ (xHints28 ++ (xHints29 ++ (xHints30 ++ (xHints31 ++ (xHints32 ++ (xHints33 ++ (xHints34 ++ (xHints35)))))))))))) = true := by
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
private theorem y_part3 :
    check (Data.x36 ++ (Data.x37 ++ (Data.x38 ++ (Data.x39 ++ (Data.x40 ++ (Data.x41 ++ (Data.x42 ++ (Data.x43 ++ (Data.x44 ++ (Data.x45)))))))))) Data.bRows (Data.y36 ++ (Data.y37 ++ (Data.y38 ++ (Data.y39 ++ (Data.y40 ++ (Data.y41 ++ (Data.y42 ++ (Data.y43 ++ (Data.y44 ++ (Data.y45)))))))))) (xHints36 ++ (xHints37 ++ (xHints38 ++ (xHints39 ++ (xHints40 ++ (xHints41 ++ (xHints42 ++ (xHints43 ++ (xHints44 ++ (xHints45)))))))))) = true := by
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

private theorem y_check : check Data.xRows Data.bRows Data.yRows xHints = true := by
  have h := check_append _ _ _ _ _ _ _ y_part0
    (check_append _ _ _ _ _ _ _ y_part1
      (check_append _ _ _ _ _ _ _ y_part2 y_part3))
  simpa only [Data.xRows, Data.yRows, xHints, List.append_assoc] using h

/-- The complete product on the published fixed matrices. -/
theorem y_product : Data.x * Data1242.second = Data.y := by
  rw [← Data.decode_bRows]
  exact product 1242 Data.xRows Data.bRows Data.yRows xHints
    Data.xRows_length Data.bRows_length y_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
