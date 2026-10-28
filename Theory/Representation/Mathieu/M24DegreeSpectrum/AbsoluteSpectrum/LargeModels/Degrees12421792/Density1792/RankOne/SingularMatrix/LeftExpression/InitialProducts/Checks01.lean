module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar01

/-!
# Exact product checks on rows 64 through 127

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block01

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t64 tb64 ts64 _ _ ts64_sum ts64_parity
  apply product_cons_b t65 tb65 ts65 _ _ ts65_sum ts65_parity
  apply product_cons_b t66 tb66 ts66 _ _ ts66_sum ts66_parity
  apply product_cons_b t67 tb67 ts67 _ _ ts67_sum ts67_parity
  apply product_cons_b t68 tb68 ts68 _ _ ts68_sum ts68_parity
  apply product_cons_b t69 tb69 ts69 _ _ ts69_sum ts69_parity
  apply product_cons_b t70 tb70 ts70 _ _ ts70_sum ts70_parity
  apply product_cons_b t71 tb71 ts71 _ _ ts71_sum ts71_parity
  apply product_cons_b t72 tb72 ts72 _ _ ts72_sum ts72_parity
  apply product_cons_b t73 tb73 ts73 _ _ ts73_sum ts73_parity
  apply product_cons_b t74 tb74 ts74 _ _ ts74_sum ts74_parity
  apply product_cons_b t75 tb75 ts75 _ _ ts75_sum ts75_parity
  apply product_cons_b t76 tb76 ts76 _ _ ts76_sum ts76_parity
  apply product_cons_b t77 tb77 ts77 _ _ ts77_sum ts77_parity
  apply product_cons_b t78 tb78 ts78 _ _ ts78_sum ts78_parity
  apply product_cons_b t79 tb79 ts79 _ _ ts79_sum ts79_parity
  apply product_cons_b t80 tb80 ts80 _ _ ts80_sum ts80_parity
  apply product_cons_b t81 tb81 ts81 _ _ ts81_sum ts81_parity
  apply product_cons_b t82 tb82 ts82 _ _ ts82_sum ts82_parity
  apply product_cons_b t83 tb83 ts83 _ _ ts83_sum ts83_parity
  apply product_cons_b t84 tb84 ts84 _ _ ts84_sum ts84_parity
  apply product_cons_b t85 tb85 ts85 _ _ ts85_sum ts85_parity
  apply product_cons_b t86 tb86 ts86 _ _ ts86_sum ts86_parity
  apply product_cons_b t87 tb87 ts87 _ _ ts87_sum ts87_parity
  apply product_cons_b t88 tb88 ts88 _ _ ts88_sum ts88_parity
  apply product_cons_b t89 tb89 ts89 _ _ ts89_sum ts89_parity
  apply product_cons_b t90 tb90 ts90 _ _ ts90_sum ts90_parity
  apply product_cons_b t91 tb91 ts91 _ _ ts91_sum ts91_parity
  apply product_cons_b t92 tb92 ts92 _ _ ts92_sum ts92_parity
  apply product_cons_b t93 tb93 ts93 _ _ ts93_sum ts93_parity
  apply product_cons_b t94 tb94 ts94 _ _ ts94_sum ts94_parity
  apply product_cons_b t95 tb95 ts95 _ _ ts95_sum ts95_parity
  apply product_cons_b t96 tb96 ts96 _ _ ts96_sum ts96_parity
  apply product_cons_b t97 tb97 ts97 _ _ ts97_sum ts97_parity
  apply product_cons_b t98 tb98 ts98 _ _ ts98_sum ts98_parity
  apply product_cons_b t99 tb99 ts99 _ _ ts99_sum ts99_parity
  apply product_cons_b t100 tb100 ts100 _ _ ts100_sum ts100_parity
  apply product_cons_b t101 tb101 ts101 _ _ ts101_sum ts101_parity
  apply product_cons_b t102 tb102 ts102 _ _ ts102_sum ts102_parity
  apply product_cons_b t103 tb103 ts103 _ _ ts103_sum ts103_parity
  apply product_cons_b t104 tb104 ts104 _ _ ts104_sum ts104_parity
  apply product_cons_b t105 tb105 ts105 _ _ ts105_sum ts105_parity
  apply product_cons_b t106 tb106 ts106 _ _ ts106_sum ts106_parity
  apply product_cons_b t107 tb107 ts107 _ _ ts107_sum ts107_parity
  apply product_cons_b t108 tb108 ts108 _ _ ts108_sum ts108_parity
  apply product_cons_b t109 tb109 ts109 _ _ ts109_sum ts109_parity
  apply product_cons_b t110 tb110 ts110 _ _ ts110_sum ts110_parity
  apply product_cons_b t111 tb111 ts111 _ _ ts111_sum ts111_parity
  apply product_cons_b t112 tb112 ts112 _ _ ts112_sum ts112_parity
  apply product_cons_b t113 tb113 ts113 _ _ ts113_sum ts113_parity
  apply product_cons_b t114 tb114 ts114 _ _ ts114_sum ts114_parity
  apply product_cons_b t115 tb115 ts115 _ _ ts115_sum ts115_parity
  apply product_cons_b t116 tb116 ts116 _ _ ts116_sum ts116_parity
  apply product_cons_b t117 tb117 ts117 _ _ ts117_sum ts117_parity
  apply product_cons_b t118 tb118 ts118 _ _ ts118_sum ts118_parity
  apply product_cons_b t119 tb119 ts119 _ _ ts119_sum ts119_parity
  apply product_cons_b t120 tb120 ts120 _ _ ts120_sum ts120_parity
  apply product_cons_b t121 tb121 ts121 _ _ ts121_sum ts121_parity
  apply product_cons_b t122 tb122 ts122 _ _ ts122_sum ts122_parity
  apply product_cons_b t123 tb123 ts123 _ _ ts123_sum ts123_parity
  apply product_cons_b t124 tb124 ts124 _ _ ts124_sum ts124_parity
  apply product_cons_b t125 tb125 ts125 _ _ ts125_sum ts125_parity
  apply product_cons_b t126 tb126 ts126 _ _ ts126_sum ts126_parity
  apply product_cons_b t127 tb127 ts127 _ _ ts127_sum ts127_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d64 da64 ds64 _ _ ds64_sum ds64_parity
  apply product_cons_a d65 da65 ds65 _ _ ds65_sum ds65_parity
  apply product_cons_a d66 da66 ds66 _ _ ds66_sum ds66_parity
  apply product_cons_a d67 da67 ds67 _ _ ds67_sum ds67_parity
  apply product_cons_a d68 da68 ds68 _ _ ds68_sum ds68_parity
  apply product_cons_a d69 da69 ds69 _ _ ds69_sum ds69_parity
  apply product_cons_a d70 da70 ds70 _ _ ds70_sum ds70_parity
  apply product_cons_a d71 da71 ds71 _ _ ds71_sum ds71_parity
  apply product_cons_a d72 da72 ds72 _ _ ds72_sum ds72_parity
  apply product_cons_a d73 da73 ds73 _ _ ds73_sum ds73_parity
  apply product_cons_a d74 da74 ds74 _ _ ds74_sum ds74_parity
  apply product_cons_a d75 da75 ds75 _ _ ds75_sum ds75_parity
  apply product_cons_a d76 da76 ds76 _ _ ds76_sum ds76_parity
  apply product_cons_a d77 da77 ds77 _ _ ds77_sum ds77_parity
  apply product_cons_a d78 da78 ds78 _ _ ds78_sum ds78_parity
  apply product_cons_a d79 da79 ds79 _ _ ds79_sum ds79_parity
  apply product_cons_a d80 da80 ds80 _ _ ds80_sum ds80_parity
  apply product_cons_a d81 da81 ds81 _ _ ds81_sum ds81_parity
  apply product_cons_a d82 da82 ds82 _ _ ds82_sum ds82_parity
  apply product_cons_a d83 da83 ds83 _ _ ds83_sum ds83_parity
  apply product_cons_a d84 da84 ds84 _ _ ds84_sum ds84_parity
  apply product_cons_a d85 da85 ds85 _ _ ds85_sum ds85_parity
  apply product_cons_a d86 da86 ds86 _ _ ds86_sum ds86_parity
  apply product_cons_a d87 da87 ds87 _ _ ds87_sum ds87_parity
  apply product_cons_a d88 da88 ds88 _ _ ds88_sum ds88_parity
  apply product_cons_a d89 da89 ds89 _ _ ds89_sum ds89_parity
  apply product_cons_a d90 da90 ds90 _ _ ds90_sum ds90_parity
  apply product_cons_a d91 da91 ds91 _ _ ds91_sum ds91_parity
  apply product_cons_a d92 da92 ds92 _ _ ds92_sum ds92_parity
  apply product_cons_a d93 da93 ds93 _ _ ds93_sum ds93_parity
  apply product_cons_a d94 da94 ds94 _ _ ds94_sum ds94_parity
  apply product_cons_a d95 da95 ds95 _ _ ds95_sum ds95_parity
  apply product_cons_a d96 da96 ds96 _ _ ds96_sum ds96_parity
  apply product_cons_a d97 da97 ds97 _ _ ds97_sum ds97_parity
  apply product_cons_a d98 da98 ds98 _ _ ds98_sum ds98_parity
  apply product_cons_a d99 da99 ds99 _ _ ds99_sum ds99_parity
  apply product_cons_a d100 da100 ds100 _ _ ds100_sum ds100_parity
  apply product_cons_a d101 da101 ds101 _ _ ds101_sum ds101_parity
  apply product_cons_a d102 da102 ds102 _ _ ds102_sum ds102_parity
  apply product_cons_a d103 da103 ds103 _ _ ds103_sum ds103_parity
  apply product_cons_a d104 da104 ds104 _ _ ds104_sum ds104_parity
  apply product_cons_a d105 da105 ds105 _ _ ds105_sum ds105_parity
  apply product_cons_a d106 da106 ds106 _ _ ds106_sum ds106_parity
  apply product_cons_a d107 da107 ds107 _ _ ds107_sum ds107_parity
  apply product_cons_a d108 da108 ds108 _ _ ds108_sum ds108_parity
  apply product_cons_a d109 da109 ds109 _ _ ds109_sum ds109_parity
  apply product_cons_a d110 da110 ds110 _ _ ds110_sum ds110_parity
  apply product_cons_a d111 da111 ds111 _ _ ds111_sum ds111_parity
  apply product_cons_a d112 da112 ds112 _ _ ds112_sum ds112_parity
  apply product_cons_a d113 da113 ds113 _ _ ds113_sum ds113_parity
  apply product_cons_a d114 da114 ds114 _ _ ds114_sum ds114_parity
  apply product_cons_a d115 da115 ds115 _ _ ds115_sum ds115_parity
  apply product_cons_a d116 da116 ds116 _ _ ds116_sum ds116_parity
  apply product_cons_a d117 da117 ds117 _ _ ds117_sum ds117_parity
  apply product_cons_a d118 da118 ds118 _ _ ds118_sum ds118_parity
  apply product_cons_a d119 da119 ds119 _ _ ds119_sum ds119_parity
  apply product_cons_a d120 da120 ds120 _ _ ds120_sum ds120_parity
  apply product_cons_a d121 da121 ds121 _ _ ds121_sum ds121_parity
  apply product_cons_a d122 da122 ds122 _ _ ds122_sum ds122_parity
  apply product_cons_a d123 da123 ds123 _ _ ds123_sum ds123_parity
  apply product_cons_a d124 da124 ds124 _ _ ds124_sum ds124_parity
  apply product_cons_a d125 da125 ds125 _ _ ds125_sum ds125_parity
  apply product_cons_a d126 da126 ds126 _ _ ds126_sum ds126_parity
  apply product_cons_a d127 da127 ds127 _ _ ds127_sum ds127_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 64).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 64).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 64).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 64).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 64).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 64).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 64).take 64) RightCertificate.wideSecond ((tbRows.drop 64).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 64).take 64) RightCertificate.wideFirst ((daRows.drop 64).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block01
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
