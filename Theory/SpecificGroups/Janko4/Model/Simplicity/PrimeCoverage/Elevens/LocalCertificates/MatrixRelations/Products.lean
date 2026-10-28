module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations.Tables

/-!
# Kernel-checked eleven-local products

The words follow ATLAS J4G1-max7W1, attributed and transcribed in
`Elevens.Words`. Literal tables are untrusted witnesses: `decide +kernel`
checks their products and `decode_packedMul` transfers them to matrices.
-/

public section
namespace Janko4.Simplicity.Elevens.MatrixCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem product_t1 : packedMul aRows bRows = t1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t2 : packedMul t1Rows bRows = t2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t3 : packedMul t1Rows t2Rows = t3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t4 : packedMul t1Rows t3Rows = t4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t5 : packedMul t4Rows t2Rows = t5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t6p2 : packedMul t2Rows t2Rows = t6p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t6 : packedMul t6p2Rows t6p2Rows = t6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t7p2 : packedMul t5Rows t5Rows = t7p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t7p4 : packedMul t7p2Rows t7p2Rows = t7p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t7 : packedMul t7p4Rows t7p4Rows = t7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t8 : packedMul t7Rows t8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_t9 : packedMul t8Rows t6Rows = t9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t10 : packedMul t9Rows t7Rows = t10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t11 : packedMul aRows t10Rows = t11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t12 : packedMul t11Rows t10Rows = t12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t13p2 : packedMul t12Rows t12Rows = t13p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t13 : packedMul t12Rows t13p2Rows = t13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t14 : packedMul t11Rows t11Rows = t14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t15 : packedMul t13Rows t14Rows = t15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t16p2 : packedMul t11Rows t11Rows = t14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t16p3 : packedMul t11Rows t14Rows = t16p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t16 : packedMul t16p3Rows t16p3Rows = t16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t17 : packedMul t16Rows t15Rows = t17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t18p2 : packedMul t17Rows t17Rows = t18p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t18p3 : packedMul t17Rows t18p2Rows = t18p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t18p5 : packedMul t18p2Rows t18p3Rows = t18p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t18p10 : packedMul t18p5Rows t18p5Rows = t18p10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t18 : packedMul t18p10Rows t18p10Rows = t18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t19 : packedMul t18Rows bRows = t19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t20 : packedMul bRows t18Rows = t20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t21 : packedMul t20Rows t21Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_t22 : packedMul t21Rows t19Rows = t22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t23p2 : packedMul t22Rows t22Rows = t23p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t23 : packedMul t22Rows t23p2Rows = t23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t24 : packedMul t17Rows t23Rows = t24Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t25 : packedMul t17Rows t24Rows = t25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t26p2 : packedMul t25Rows t25Rows = t26p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t26p3 : packedMul t25Rows t26p2Rows = t26p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t26p4 : packedMul t26p2Rows t26p2Rows = t26p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t26 : packedMul t26p3Rows t26p4Rows = t26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t27 : packedMul t17Rows t27Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_t28 : packedMul t27Rows t23Rows = t28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t29 : packedMul t23Rows t28Rows = t29Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t30p2 : packedMul t17Rows t17Rows = t18p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t30p4 : packedMul t18p2Rows t18p2Rows = t30p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t30 : packedMul t30p4Rows t30p4Rows = t30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t31 : packedMul t30Rows t29Rows = t31Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t32 : packedMul t31Rows t32Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_t33 : packedMul aRows t17Rows = t33Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t34 : packedMul t32Rows t26Rows = t34Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_t35 : packedMul t34Rows t31Rows = t35Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15p2 : packedMul t33Rows t33Rows = v15p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15p3 : packedMul t33Rows v15p2Rows = v15p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15p4 : packedMul v15p2Rows v15p2Rows = v15p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15p7 : packedMul v15p3Rows v15p4Rows = v15p7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15p8 : packedMul v15p4Rows v15p4Rows = v15p8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_v15 : packedMul v15p7Rows v15p8Rows = v15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_uv15 : packedMul t35Rows v15Rows = uv15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x : packedMul uv15Rows uv15Rows = xRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_vi : packedMul t33Rows viRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_vix : packedMul viRows xRows = vixRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y : packedMul vixRows t33Rows = yRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xi : packedMul xRows xiRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_yi : packedMul yRows yiRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_xiyi : packedMul xiRows yiRows = xiyiRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_xiyix : packedMul xiyiRows xRows = xiyixRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z : packedMul xiyixRows yRows = zRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x11p2 : packedMul xRows xRows = x11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x11p3 : packedMul xRows x11p2Rows = x11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x11p5 : packedMul x11p2Rows x11p3Rows = x11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x11p6 : packedMul x11p3Rows x11p3Rows = x11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x11 : packedMul x11p5Rows x11p6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_y11p2 : packedMul yRows yRows = y11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y11p3 : packedMul yRows y11p2Rows = y11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y11p5 : packedMul y11p2Rows y11p3Rows = y11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y11p6 : packedMul y11p3Rows y11p3Rows = y11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y11 : packedMul y11p5Rows y11p6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_z11p2 : packedMul zRows zRows = z11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z11p3 : packedMul zRows z11p2Rows = z11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z11p5 : packedMul z11p2Rows z11p3Rows = z11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z11p6 : packedMul z11p3Rows z11p3Rows = z11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z11 : packedMul z11p5Rows z11p6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_xz : packedMul xRows zRows = xzRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_zx : packedMul zRows xRows = xzRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_yz : packedMul yRows zRows = yzRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_zy : packedMul zRows yRows = yzRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ui : packedMul t35Rows uiRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

theorem product_uix : packedMul uiRows xRows = uixRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_ux : packedMul uixRows t35Rows = uxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_uiy : packedMul uiRows yRows = uiyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_uy : packedMul uiyRows t35Rows = uyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_uiz : packedMul uiRows zRows = uizRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_uz : packedMul uizRows t35Rows = zRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_viy : packedMul viRows yRows = viyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_vy : packedMul viyRows t33Rows = vyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_viz : packedMul viRows zRows = vizRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_vz : packedMul vizRows t33Rows = z11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y3p2 : packedMul yRows yRows = y11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y3 : packedMul yRows y11p2Rows = y11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7p2 : packedMul xRows xRows = x11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7p3 : packedMul xRows x11p2Rows = x11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7p4 : packedMul x11p2Rows x11p2Rows = x7p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x7 : packedMul x11p3Rows x7p4Rows = x7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10p2 : packedMul yRows yRows = y11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10p3 : packedMul yRows y11p2Rows = y11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10p5 : packedMul y11p2Rows y11p3Rows = y11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_y10 : packedMul y11p5Rows y11p5Rows = yiRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z2 : packedMul zRows zRows = z11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x5p2 : packedMul xRows xRows = x11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x5p3 : packedMul xRows x11p2Rows = x11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_x5 : packedMul x11p2Rows x11p3Rows = x11p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z4p2 : packedMul zRows zRows = z11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z4 : packedMul z11p2Rows z11p2Rows = z4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z6p2 : packedMul zRows zRows = z11p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z6p3 : packedMul zRows z11p2Rows = z11p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_z6 : packedMul z11p3Rows z11p3Rows = z11p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_rhsux : packedMul y11p3Rows zRows = uxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_rhsuy1 : packedMul x7Rows yiRows = rhsuy1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_rhsuy : packedMul rhsuy1Rows z11p2Rows = uyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_rhsvy1 : packedMul x11p5Rows yRows = rhsvy1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_rhsvy : packedMul rhsvy1Rows z4Rows = vyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.Elevens.MatrixCertificates
