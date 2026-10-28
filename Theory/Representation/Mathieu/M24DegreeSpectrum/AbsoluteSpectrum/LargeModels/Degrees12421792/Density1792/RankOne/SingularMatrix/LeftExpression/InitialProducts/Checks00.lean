module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar00

/-!
# Exact product checks on rows 0 through 63

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block00

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t0 tb0 ts0 _ _ ts0_sum ts0_parity
  apply product_cons_b t1 tb1 ts1 _ _ ts1_sum ts1_parity
  apply product_cons_b t2 tb2 ts2 _ _ ts2_sum ts2_parity
  apply product_cons_b t3 tb3 ts3 _ _ ts3_sum ts3_parity
  apply product_cons_b t4 tb4 ts4 _ _ ts4_sum ts4_parity
  apply product_cons_b t5 tb5 ts5 _ _ ts5_sum ts5_parity
  apply product_cons_b t6 tb6 ts6 _ _ ts6_sum ts6_parity
  apply product_cons_b t7 tb7 ts7 _ _ ts7_sum ts7_parity
  apply product_cons_b t8 tb8 ts8 _ _ ts8_sum ts8_parity
  apply product_cons_b t9 tb9 ts9 _ _ ts9_sum ts9_parity
  apply product_cons_b t10 tb10 ts10 _ _ ts10_sum ts10_parity
  apply product_cons_b t11 tb11 ts11 _ _ ts11_sum ts11_parity
  apply product_cons_b t12 tb12 ts12 _ _ ts12_sum ts12_parity
  apply product_cons_b t13 tb13 ts13 _ _ ts13_sum ts13_parity
  apply product_cons_b t14 tb14 ts14 _ _ ts14_sum ts14_parity
  apply product_cons_b t15 tb15 ts15 _ _ ts15_sum ts15_parity
  apply product_cons_b t16 tb16 ts16 _ _ ts16_sum ts16_parity
  apply product_cons_b t17 tb17 ts17 _ _ ts17_sum ts17_parity
  apply product_cons_b t18 tb18 ts18 _ _ ts18_sum ts18_parity
  apply product_cons_b t19 tb19 ts19 _ _ ts19_sum ts19_parity
  apply product_cons_b t20 tb20 ts20 _ _ ts20_sum ts20_parity
  apply product_cons_b t21 tb21 ts21 _ _ ts21_sum ts21_parity
  apply product_cons_b t22 tb22 ts22 _ _ ts22_sum ts22_parity
  apply product_cons_b t23 tb23 ts23 _ _ ts23_sum ts23_parity
  apply product_cons_b t24 tb24 ts24 _ _ ts24_sum ts24_parity
  apply product_cons_b t25 tb25 ts25 _ _ ts25_sum ts25_parity
  apply product_cons_b t26 tb26 ts26 _ _ ts26_sum ts26_parity
  apply product_cons_b t27 tb27 ts27 _ _ ts27_sum ts27_parity
  apply product_cons_b t28 tb28 ts28 _ _ ts28_sum ts28_parity
  apply product_cons_b t29 tb29 ts29 _ _ ts29_sum ts29_parity
  apply product_cons_b t30 tb30 ts30 _ _ ts30_sum ts30_parity
  apply product_cons_b t31 tb31 ts31 _ _ ts31_sum ts31_parity
  apply product_cons_b t32 tb32 ts32 _ _ ts32_sum ts32_parity
  apply product_cons_b t33 tb33 ts33 _ _ ts33_sum ts33_parity
  apply product_cons_b t34 tb34 ts34 _ _ ts34_sum ts34_parity
  apply product_cons_b t35 tb35 ts35 _ _ ts35_sum ts35_parity
  apply product_cons_b t36 tb36 ts36 _ _ ts36_sum ts36_parity
  apply product_cons_b t37 tb37 ts37 _ _ ts37_sum ts37_parity
  apply product_cons_b t38 tb38 ts38 _ _ ts38_sum ts38_parity
  apply product_cons_b t39 tb39 ts39 _ _ ts39_sum ts39_parity
  apply product_cons_b t40 tb40 ts40 _ _ ts40_sum ts40_parity
  apply product_cons_b t41 tb41 ts41 _ _ ts41_sum ts41_parity
  apply product_cons_b t42 tb42 ts42 _ _ ts42_sum ts42_parity
  apply product_cons_b t43 tb43 ts43 _ _ ts43_sum ts43_parity
  apply product_cons_b t44 tb44 ts44 _ _ ts44_sum ts44_parity
  apply product_cons_b t45 tb45 ts45 _ _ ts45_sum ts45_parity
  apply product_cons_b t46 tb46 ts46 _ _ ts46_sum ts46_parity
  apply product_cons_b t47 tb47 ts47 _ _ ts47_sum ts47_parity
  apply product_cons_b t48 tb48 ts48 _ _ ts48_sum ts48_parity
  apply product_cons_b t49 tb49 ts49 _ _ ts49_sum ts49_parity
  apply product_cons_b t50 tb50 ts50 _ _ ts50_sum ts50_parity
  apply product_cons_b t51 tb51 ts51 _ _ ts51_sum ts51_parity
  apply product_cons_b t52 tb52 ts52 _ _ ts52_sum ts52_parity
  apply product_cons_b t53 tb53 ts53 _ _ ts53_sum ts53_parity
  apply product_cons_b t54 tb54 ts54 _ _ ts54_sum ts54_parity
  apply product_cons_b t55 tb55 ts55 _ _ ts55_sum ts55_parity
  apply product_cons_b t56 tb56 ts56 _ _ ts56_sum ts56_parity
  apply product_cons_b t57 tb57 ts57 _ _ ts57_sum ts57_parity
  apply product_cons_b t58 tb58 ts58 _ _ ts58_sum ts58_parity
  apply product_cons_b t59 tb59 ts59 _ _ ts59_sum ts59_parity
  apply product_cons_b t60 tb60 ts60 _ _ ts60_sum ts60_parity
  apply product_cons_b t61 tb61 ts61 _ _ ts61_sum ts61_parity
  apply product_cons_b t62 tb62 ts62 _ _ ts62_sum ts62_parity
  apply product_cons_b t63 tb63 ts63 _ _ ts63_sum ts63_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d0 da0 ds0 _ _ ds0_sum ds0_parity
  apply product_cons_a d1 da1 ds1 _ _ ds1_sum ds1_parity
  apply product_cons_a d2 da2 ds2 _ _ ds2_sum ds2_parity
  apply product_cons_a d3 da3 ds3 _ _ ds3_sum ds3_parity
  apply product_cons_a d4 da4 ds4 _ _ ds4_sum ds4_parity
  apply product_cons_a d5 da5 ds5 _ _ ds5_sum ds5_parity
  apply product_cons_a d6 da6 ds6 _ _ ds6_sum ds6_parity
  apply product_cons_a d7 da7 ds7 _ _ ds7_sum ds7_parity
  apply product_cons_a d8 da8 ds8 _ _ ds8_sum ds8_parity
  apply product_cons_a d9 da9 ds9 _ _ ds9_sum ds9_parity
  apply product_cons_a d10 da10 ds10 _ _ ds10_sum ds10_parity
  apply product_cons_a d11 da11 ds11 _ _ ds11_sum ds11_parity
  apply product_cons_a d12 da12 ds12 _ _ ds12_sum ds12_parity
  apply product_cons_a d13 da13 ds13 _ _ ds13_sum ds13_parity
  apply product_cons_a d14 da14 ds14 _ _ ds14_sum ds14_parity
  apply product_cons_a d15 da15 ds15 _ _ ds15_sum ds15_parity
  apply product_cons_a d16 da16 ds16 _ _ ds16_sum ds16_parity
  apply product_cons_a d17 da17 ds17 _ _ ds17_sum ds17_parity
  apply product_cons_a d18 da18 ds18 _ _ ds18_sum ds18_parity
  apply product_cons_a d19 da19 ds19 _ _ ds19_sum ds19_parity
  apply product_cons_a d20 da20 ds20 _ _ ds20_sum ds20_parity
  apply product_cons_a d21 da21 ds21 _ _ ds21_sum ds21_parity
  apply product_cons_a d22 da22 ds22 _ _ ds22_sum ds22_parity
  apply product_cons_a d23 da23 ds23 _ _ ds23_sum ds23_parity
  apply product_cons_a d24 da24 ds24 _ _ ds24_sum ds24_parity
  apply product_cons_a d25 da25 ds25 _ _ ds25_sum ds25_parity
  apply product_cons_a d26 da26 ds26 _ _ ds26_sum ds26_parity
  apply product_cons_a d27 da27 ds27 _ _ ds27_sum ds27_parity
  apply product_cons_a d28 da28 ds28 _ _ ds28_sum ds28_parity
  apply product_cons_a d29 da29 ds29 _ _ ds29_sum ds29_parity
  apply product_cons_a d30 da30 ds30 _ _ ds30_sum ds30_parity
  apply product_cons_a d31 da31 ds31 _ _ ds31_sum ds31_parity
  apply product_cons_a d32 da32 ds32 _ _ ds32_sum ds32_parity
  apply product_cons_a d33 da33 ds33 _ _ ds33_sum ds33_parity
  apply product_cons_a d34 da34 ds34 _ _ ds34_sum ds34_parity
  apply product_cons_a d35 da35 ds35 _ _ ds35_sum ds35_parity
  apply product_cons_a d36 da36 ds36 _ _ ds36_sum ds36_parity
  apply product_cons_a d37 da37 ds37 _ _ ds37_sum ds37_parity
  apply product_cons_a d38 da38 ds38 _ _ ds38_sum ds38_parity
  apply product_cons_a d39 da39 ds39 _ _ ds39_sum ds39_parity
  apply product_cons_a d40 da40 ds40 _ _ ds40_sum ds40_parity
  apply product_cons_a d41 da41 ds41 _ _ ds41_sum ds41_parity
  apply product_cons_a d42 da42 ds42 _ _ ds42_sum ds42_parity
  apply product_cons_a d43 da43 ds43 _ _ ds43_sum ds43_parity
  apply product_cons_a d44 da44 ds44 _ _ ds44_sum ds44_parity
  apply product_cons_a d45 da45 ds45 _ _ ds45_sum ds45_parity
  apply product_cons_a d46 da46 ds46 _ _ ds46_sum ds46_parity
  apply product_cons_a d47 da47 ds47 _ _ ds47_sum ds47_parity
  apply product_cons_a d48 da48 ds48 _ _ ds48_sum ds48_parity
  apply product_cons_a d49 da49 ds49 _ _ ds49_sum ds49_parity
  apply product_cons_a d50 da50 ds50 _ _ ds50_sum ds50_parity
  apply product_cons_a d51 da51 ds51 _ _ ds51_sum ds51_parity
  apply product_cons_a d52 da52 ds52 _ _ ds52_sum ds52_parity
  apply product_cons_a d53 da53 ds53 _ _ ds53_sum ds53_parity
  apply product_cons_a d54 da54 ds54 _ _ ds54_sum ds54_parity
  apply product_cons_a d55 da55 ds55 _ _ ds55_sum ds55_parity
  apply product_cons_a d56 da56 ds56 _ _ ds56_sum ds56_parity
  apply product_cons_a d57 da57 ds57 _ _ ds57_sum ds57_parity
  apply product_cons_a d58 da58 ds58 _ _ ds58_sum ds58_parity
  apply product_cons_a d59 da59 ds59 _ _ ds59_sum ds59_parity
  apply product_cons_a d60 da60 ds60 _ _ ds60_sum ds60_parity
  apply product_cons_a d61 da61 ds61 _ _ ds61_sum ds61_parity
  apply product_cons_a d62 da62 ds62 _ _ ds62_sum ds62_parity
  apply product_cons_a d63 da63 ds63 _ _ ds63_sum ds63_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 0).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 0).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 0).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 0).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 0).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 0).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 0).take 64) RightCertificate.wideSecond ((tbRows.drop 0).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 0).take 64) RightCertificate.wideFirst ((daRows.drop 0).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block00
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
