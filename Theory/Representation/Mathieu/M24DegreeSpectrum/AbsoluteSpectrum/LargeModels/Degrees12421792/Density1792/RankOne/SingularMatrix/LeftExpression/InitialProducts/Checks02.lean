module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar02

/-!
# Exact product checks on rows 128 through 191

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block02

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t128 tb128 ts128 _ _ ts128_sum ts128_parity
  apply product_cons_b t129 tb129 ts129 _ _ ts129_sum ts129_parity
  apply product_cons_b t130 tb130 ts130 _ _ ts130_sum ts130_parity
  apply product_cons_b t131 tb131 ts131 _ _ ts131_sum ts131_parity
  apply product_cons_b t132 tb132 ts132 _ _ ts132_sum ts132_parity
  apply product_cons_b t133 tb133 ts133 _ _ ts133_sum ts133_parity
  apply product_cons_b t134 tb134 ts134 _ _ ts134_sum ts134_parity
  apply product_cons_b t135 tb135 ts135 _ _ ts135_sum ts135_parity
  apply product_cons_b t136 tb136 ts136 _ _ ts136_sum ts136_parity
  apply product_cons_b t137 tb137 ts137 _ _ ts137_sum ts137_parity
  apply product_cons_b t138 tb138 ts138 _ _ ts138_sum ts138_parity
  apply product_cons_b t139 tb139 ts139 _ _ ts139_sum ts139_parity
  apply product_cons_b t140 tb140 ts140 _ _ ts140_sum ts140_parity
  apply product_cons_b t141 tb141 ts141 _ _ ts141_sum ts141_parity
  apply product_cons_b t142 tb142 ts142 _ _ ts142_sum ts142_parity
  apply product_cons_b t143 tb143 ts143 _ _ ts143_sum ts143_parity
  apply product_cons_b t144 tb144 ts144 _ _ ts144_sum ts144_parity
  apply product_cons_b t145 tb145 ts145 _ _ ts145_sum ts145_parity
  apply product_cons_b t146 tb146 ts146 _ _ ts146_sum ts146_parity
  apply product_cons_b t147 tb147 ts147 _ _ ts147_sum ts147_parity
  apply product_cons_b t148 tb148 ts148 _ _ ts148_sum ts148_parity
  apply product_cons_b t149 tb149 ts149 _ _ ts149_sum ts149_parity
  apply product_cons_b t150 tb150 ts150 _ _ ts150_sum ts150_parity
  apply product_cons_b t151 tb151 ts151 _ _ ts151_sum ts151_parity
  apply product_cons_b t152 tb152 ts152 _ _ ts152_sum ts152_parity
  apply product_cons_b t153 tb153 ts153 _ _ ts153_sum ts153_parity
  apply product_cons_b t154 tb154 ts154 _ _ ts154_sum ts154_parity
  apply product_cons_b t155 tb155 ts155 _ _ ts155_sum ts155_parity
  apply product_cons_b t156 tb156 ts156 _ _ ts156_sum ts156_parity
  apply product_cons_b t157 tb157 ts157 _ _ ts157_sum ts157_parity
  apply product_cons_b t158 tb158 ts158 _ _ ts158_sum ts158_parity
  apply product_cons_b t159 tb159 ts159 _ _ ts159_sum ts159_parity
  apply product_cons_b t160 tb160 ts160 _ _ ts160_sum ts160_parity
  apply product_cons_b t161 tb161 ts161 _ _ ts161_sum ts161_parity
  apply product_cons_b t162 tb162 ts162 _ _ ts162_sum ts162_parity
  apply product_cons_b t163 tb163 ts163 _ _ ts163_sum ts163_parity
  apply product_cons_b t164 tb164 ts164 _ _ ts164_sum ts164_parity
  apply product_cons_b t165 tb165 ts165 _ _ ts165_sum ts165_parity
  apply product_cons_b t166 tb166 ts166 _ _ ts166_sum ts166_parity
  apply product_cons_b t167 tb167 ts167 _ _ ts167_sum ts167_parity
  apply product_cons_b t168 tb168 ts168 _ _ ts168_sum ts168_parity
  apply product_cons_b t169 tb169 ts169 _ _ ts169_sum ts169_parity
  apply product_cons_b t170 tb170 ts170 _ _ ts170_sum ts170_parity
  apply product_cons_b t171 tb171 ts171 _ _ ts171_sum ts171_parity
  apply product_cons_b t172 tb172 ts172 _ _ ts172_sum ts172_parity
  apply product_cons_b t173 tb173 ts173 _ _ ts173_sum ts173_parity
  apply product_cons_b t174 tb174 ts174 _ _ ts174_sum ts174_parity
  apply product_cons_b t175 tb175 ts175 _ _ ts175_sum ts175_parity
  apply product_cons_b t176 tb176 ts176 _ _ ts176_sum ts176_parity
  apply product_cons_b t177 tb177 ts177 _ _ ts177_sum ts177_parity
  apply product_cons_b t178 tb178 ts178 _ _ ts178_sum ts178_parity
  apply product_cons_b t179 tb179 ts179 _ _ ts179_sum ts179_parity
  apply product_cons_b t180 tb180 ts180 _ _ ts180_sum ts180_parity
  apply product_cons_b t181 tb181 ts181 _ _ ts181_sum ts181_parity
  apply product_cons_b t182 tb182 ts182 _ _ ts182_sum ts182_parity
  apply product_cons_b t183 tb183 ts183 _ _ ts183_sum ts183_parity
  apply product_cons_b t184 tb184 ts184 _ _ ts184_sum ts184_parity
  apply product_cons_b t185 tb185 ts185 _ _ ts185_sum ts185_parity
  apply product_cons_b t186 tb186 ts186 _ _ ts186_sum ts186_parity
  apply product_cons_b t187 tb187 ts187 _ _ ts187_sum ts187_parity
  apply product_cons_b t188 tb188 ts188 _ _ ts188_sum ts188_parity
  apply product_cons_b t189 tb189 ts189 _ _ ts189_sum ts189_parity
  apply product_cons_b t190 tb190 ts190 _ _ ts190_sum ts190_parity
  apply product_cons_b t191 tb191 ts191 _ _ ts191_sum ts191_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d128 da128 ds128 _ _ ds128_sum ds128_parity
  apply product_cons_a d129 da129 ds129 _ _ ds129_sum ds129_parity
  apply product_cons_a d130 da130 ds130 _ _ ds130_sum ds130_parity
  apply product_cons_a d131 da131 ds131 _ _ ds131_sum ds131_parity
  apply product_cons_a d132 da132 ds132 _ _ ds132_sum ds132_parity
  apply product_cons_a d133 da133 ds133 _ _ ds133_sum ds133_parity
  apply product_cons_a d134 da134 ds134 _ _ ds134_sum ds134_parity
  apply product_cons_a d135 da135 ds135 _ _ ds135_sum ds135_parity
  apply product_cons_a d136 da136 ds136 _ _ ds136_sum ds136_parity
  apply product_cons_a d137 da137 ds137 _ _ ds137_sum ds137_parity
  apply product_cons_a d138 da138 ds138 _ _ ds138_sum ds138_parity
  apply product_cons_a d139 da139 ds139 _ _ ds139_sum ds139_parity
  apply product_cons_a d140 da140 ds140 _ _ ds140_sum ds140_parity
  apply product_cons_a d141 da141 ds141 _ _ ds141_sum ds141_parity
  apply product_cons_a d142 da142 ds142 _ _ ds142_sum ds142_parity
  apply product_cons_a d143 da143 ds143 _ _ ds143_sum ds143_parity
  apply product_cons_a d144 da144 ds144 _ _ ds144_sum ds144_parity
  apply product_cons_a d145 da145 ds145 _ _ ds145_sum ds145_parity
  apply product_cons_a d146 da146 ds146 _ _ ds146_sum ds146_parity
  apply product_cons_a d147 da147 ds147 _ _ ds147_sum ds147_parity
  apply product_cons_a d148 da148 ds148 _ _ ds148_sum ds148_parity
  apply product_cons_a d149 da149 ds149 _ _ ds149_sum ds149_parity
  apply product_cons_a d150 da150 ds150 _ _ ds150_sum ds150_parity
  apply product_cons_a d151 da151 ds151 _ _ ds151_sum ds151_parity
  apply product_cons_a d152 da152 ds152 _ _ ds152_sum ds152_parity
  apply product_cons_a d153 da153 ds153 _ _ ds153_sum ds153_parity
  apply product_cons_a d154 da154 ds154 _ _ ds154_sum ds154_parity
  apply product_cons_a d155 da155 ds155 _ _ ds155_sum ds155_parity
  apply product_cons_a d156 da156 ds156 _ _ ds156_sum ds156_parity
  apply product_cons_a d157 da157 ds157 _ _ ds157_sum ds157_parity
  apply product_cons_a d158 da158 ds158 _ _ ds158_sum ds158_parity
  apply product_cons_a d159 da159 ds159 _ _ ds159_sum ds159_parity
  apply product_cons_a d160 da160 ds160 _ _ ds160_sum ds160_parity
  apply product_cons_a d161 da161 ds161 _ _ ds161_sum ds161_parity
  apply product_cons_a d162 da162 ds162 _ _ ds162_sum ds162_parity
  apply product_cons_a d163 da163 ds163 _ _ ds163_sum ds163_parity
  apply product_cons_a d164 da164 ds164 _ _ ds164_sum ds164_parity
  apply product_cons_a d165 da165 ds165 _ _ ds165_sum ds165_parity
  apply product_cons_a d166 da166 ds166 _ _ ds166_sum ds166_parity
  apply product_cons_a d167 da167 ds167 _ _ ds167_sum ds167_parity
  apply product_cons_a d168 da168 ds168 _ _ ds168_sum ds168_parity
  apply product_cons_a d169 da169 ds169 _ _ ds169_sum ds169_parity
  apply product_cons_a d170 da170 ds170 _ _ ds170_sum ds170_parity
  apply product_cons_a d171 da171 ds171 _ _ ds171_sum ds171_parity
  apply product_cons_a d172 da172 ds172 _ _ ds172_sum ds172_parity
  apply product_cons_a d173 da173 ds173 _ _ ds173_sum ds173_parity
  apply product_cons_a d174 da174 ds174 _ _ ds174_sum ds174_parity
  apply product_cons_a d175 da175 ds175 _ _ ds175_sum ds175_parity
  apply product_cons_a d176 da176 ds176 _ _ ds176_sum ds176_parity
  apply product_cons_a d177 da177 ds177 _ _ ds177_sum ds177_parity
  apply product_cons_a d178 da178 ds178 _ _ ds178_sum ds178_parity
  apply product_cons_a d179 da179 ds179 _ _ ds179_sum ds179_parity
  apply product_cons_a d180 da180 ds180 _ _ ds180_sum ds180_parity
  apply product_cons_a d181 da181 ds181 _ _ ds181_sum ds181_parity
  apply product_cons_a d182 da182 ds182 _ _ ds182_sum ds182_parity
  apply product_cons_a d183 da183 ds183 _ _ ds183_sum ds183_parity
  apply product_cons_a d184 da184 ds184 _ _ ds184_sum ds184_parity
  apply product_cons_a d185 da185 ds185 _ _ ds185_sum ds185_parity
  apply product_cons_a d186 da186 ds186 _ _ ds186_sum ds186_parity
  apply product_cons_a d187 da187 ds187 _ _ ds187_sum ds187_parity
  apply product_cons_a d188 da188 ds188 _ _ ds188_sum ds188_parity
  apply product_cons_a d189 da189 ds189 _ _ ds189_sum ds189_parity
  apply product_cons_a d190 da190 ds190 _ _ ds190_sum ds190_parity
  apply product_cons_a d191 da191 ds191 _ _ ds191_sum ds191_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 128).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 128).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 128).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 128).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 128).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 128).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 128).take 64) RightCertificate.wideSecond ((tbRows.drop 128).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 128).take 64) RightCertificate.wideFirst ((daRows.drop 128).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block02
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
