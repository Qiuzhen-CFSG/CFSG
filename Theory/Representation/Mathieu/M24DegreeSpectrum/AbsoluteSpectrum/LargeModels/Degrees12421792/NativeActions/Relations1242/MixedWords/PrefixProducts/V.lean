module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixProducts.Hints
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# The literal Z*Y = V prefix product

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
private theorem v_part0 :
    check (Data.z00 ++ (Data.z01 ++ (Data.z02 ++ (Data.z03 ++ (Data.z04 ++ (Data.z05 ++ (Data.z06 ++ (Data.z07 ++ (Data.z08 ++ (Data.z09 ++ (Data.z10 ++ (Data.z11)))))))))))) Data.yRows (Data.v00 ++ (Data.v01 ++ (Data.v02 ++ (Data.v03 ++ (Data.v04 ++ (Data.v05 ++ (Data.v06 ++ (Data.v07 ++ (Data.v08 ++ (Data.v09 ++ (Data.v10 ++ (Data.v11)))))))))))) (zHints00 ++ (zHints01 ++ (zHints02 ++ (zHints03 ++ (zHints04 ++ (zHints05 ++ (zHints06 ++ (zHints07 ++ (zHints08 ++ (zHints09 ++ (zHints10 ++ (zHints11)))))))))))) = true := by
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
private theorem v_part1 :
    check (Data.z12 ++ (Data.z13 ++ (Data.z14 ++ (Data.z15 ++ (Data.z16 ++ (Data.z17 ++ (Data.z18 ++ (Data.z19 ++ (Data.z20 ++ (Data.z21 ++ (Data.z22 ++ (Data.z23)))))))))))) Data.yRows (Data.v12 ++ (Data.v13 ++ (Data.v14 ++ (Data.v15 ++ (Data.v16 ++ (Data.v17 ++ (Data.v18 ++ (Data.v19 ++ (Data.v20 ++ (Data.v21 ++ (Data.v22 ++ (Data.v23)))))))))))) (zHints12 ++ (zHints13 ++ (zHints14 ++ (zHints15 ++ (zHints16 ++ (zHints17 ++ (zHints18 ++ (zHints19 ++ (zHints20 ++ (zHints21 ++ (zHints22 ++ (zHints23)))))))))))) = true := by
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
private theorem v_part2 :
    check (Data.z24 ++ (Data.z25 ++ (Data.z26 ++ (Data.z27 ++ (Data.z28 ++ (Data.z29 ++ (Data.z30 ++ (Data.z31 ++ (Data.z32 ++ (Data.z33 ++ (Data.z34 ++ (Data.z35)))))))))))) Data.yRows (Data.v24 ++ (Data.v25 ++ (Data.v26 ++ (Data.v27 ++ (Data.v28 ++ (Data.v29 ++ (Data.v30 ++ (Data.v31 ++ (Data.v32 ++ (Data.v33 ++ (Data.v34 ++ (Data.v35)))))))))))) (zHints24 ++ (zHints25 ++ (zHints26 ++ (zHints27 ++ (zHints28 ++ (zHints29 ++ (zHints30 ++ (zHints31 ++ (zHints32 ++ (zHints33 ++ (zHints34 ++ (zHints35)))))))))))) = true := by
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
private theorem v_part3 :
    check (Data.z36 ++ (Data.z37 ++ (Data.z38))) Data.yRows (Data.v36 ++ (Data.v37 ++ (Data.v38))) (zHints36 ++ (zHints37 ++ (zHints38))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem v_part4 :
    check (Data.z39 ++ (Data.z40 ++ (Data.z41))) Data.yRows (Data.v39 ++ (Data.v40 ++ (Data.v41))) (zHints39 ++ (zHints40 ++ (zHints41))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem v_part5 :
    check (Data.z42 ++ (Data.z43 ++ (Data.z44))) Data.yRows (Data.v42 ++ (Data.v43 ++ (Data.v44))) (zHints42 ++ (zHints43 ++ (zHints44))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem v_part6 :
    check (Data.z45) Data.yRows (Data.v45) (zHints45) = true := by
  decide +kernel

private theorem v_check : check Data.zRows Data.yRows Data.vRows zHints = true := by
  have h := check_append _ _ _ _ _ _ _ v_part0
    (check_append _ _ _ _ _ _ _ v_part1
      (check_append _ _ _ _ _ _ _ v_part2
        (check_append _ _ _ _ _ _ _ v_part3
          (check_append _ _ _ _ _ _ _ v_part4
            (check_append _ _ _ _ _ _ _ v_part5 v_part6)))))
  simpa only [Data.zRows, Data.vRows, zHints, List.append_assoc] using h

/-- The complete product on the published fixed matrices. -/
theorem v_product : Data.z * Data.y = Data.v := by
  exact product 1242 Data.zRows Data.yRows Data.vRows zHints
    Data.zRows_length Data.yRows_length v_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
