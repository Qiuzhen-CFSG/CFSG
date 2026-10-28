module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar03

/-!
# Exact product checks on rows 192 through 255

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block03

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t192 tb192 ts192 _ _ ts192_sum ts192_parity
  apply product_cons_b t193 tb193 ts193 _ _ ts193_sum ts193_parity
  apply product_cons_b t194 tb194 ts194 _ _ ts194_sum ts194_parity
  apply product_cons_b t195 tb195 ts195 _ _ ts195_sum ts195_parity
  apply product_cons_b t196 tb196 ts196 _ _ ts196_sum ts196_parity
  apply product_cons_b t197 tb197 ts197 _ _ ts197_sum ts197_parity
  apply product_cons_b t198 tb198 ts198 _ _ ts198_sum ts198_parity
  apply product_cons_b t199 tb199 ts199 _ _ ts199_sum ts199_parity
  apply product_cons_b t200 tb200 ts200 _ _ ts200_sum ts200_parity
  apply product_cons_b t201 tb201 ts201 _ _ ts201_sum ts201_parity
  apply product_cons_b t202 tb202 ts202 _ _ ts202_sum ts202_parity
  apply product_cons_b t203 tb203 ts203 _ _ ts203_sum ts203_parity
  apply product_cons_b t204 tb204 ts204 _ _ ts204_sum ts204_parity
  apply product_cons_b t205 tb205 ts205 _ _ ts205_sum ts205_parity
  apply product_cons_b t206 tb206 ts206 _ _ ts206_sum ts206_parity
  apply product_cons_b t207 tb207 ts207 _ _ ts207_sum ts207_parity
  apply product_cons_b t208 tb208 ts208 _ _ ts208_sum ts208_parity
  apply product_cons_b t209 tb209 ts209 _ _ ts209_sum ts209_parity
  apply product_cons_b t210 tb210 ts210 _ _ ts210_sum ts210_parity
  apply product_cons_b t211 tb211 ts211 _ _ ts211_sum ts211_parity
  apply product_cons_b t212 tb212 ts212 _ _ ts212_sum ts212_parity
  apply product_cons_b t213 tb213 ts213 _ _ ts213_sum ts213_parity
  apply product_cons_b t214 tb214 ts214 _ _ ts214_sum ts214_parity
  apply product_cons_b t215 tb215 ts215 _ _ ts215_sum ts215_parity
  apply product_cons_b t216 tb216 ts216 _ _ ts216_sum ts216_parity
  apply product_cons_b t217 tb217 ts217 _ _ ts217_sum ts217_parity
  apply product_cons_b t218 tb218 ts218 _ _ ts218_sum ts218_parity
  apply product_cons_b t219 tb219 ts219 _ _ ts219_sum ts219_parity
  apply product_cons_b t220 tb220 ts220 _ _ ts220_sum ts220_parity
  apply product_cons_b t221 tb221 ts221 _ _ ts221_sum ts221_parity
  apply product_cons_b t222 tb222 ts222 _ _ ts222_sum ts222_parity
  apply product_cons_b t223 tb223 ts223 _ _ ts223_sum ts223_parity
  apply product_cons_b t224 tb224 ts224 _ _ ts224_sum ts224_parity
  apply product_cons_b t225 tb225 ts225 _ _ ts225_sum ts225_parity
  apply product_cons_b t226 tb226 ts226 _ _ ts226_sum ts226_parity
  apply product_cons_b t227 tb227 ts227 _ _ ts227_sum ts227_parity
  apply product_cons_b t228 tb228 ts228 _ _ ts228_sum ts228_parity
  apply product_cons_b t229 tb229 ts229 _ _ ts229_sum ts229_parity
  apply product_cons_b t230 tb230 ts230 _ _ ts230_sum ts230_parity
  apply product_cons_b t231 tb231 ts231 _ _ ts231_sum ts231_parity
  apply product_cons_b t232 tb232 ts232 _ _ ts232_sum ts232_parity
  apply product_cons_b t233 tb233 ts233 _ _ ts233_sum ts233_parity
  apply product_cons_b t234 tb234 ts234 _ _ ts234_sum ts234_parity
  apply product_cons_b t235 tb235 ts235 _ _ ts235_sum ts235_parity
  apply product_cons_b t236 tb236 ts236 _ _ ts236_sum ts236_parity
  apply product_cons_b t237 tb237 ts237 _ _ ts237_sum ts237_parity
  apply product_cons_b t238 tb238 ts238 _ _ ts238_sum ts238_parity
  apply product_cons_b t239 tb239 ts239 _ _ ts239_sum ts239_parity
  apply product_cons_b t240 tb240 ts240 _ _ ts240_sum ts240_parity
  apply product_cons_b t241 tb241 ts241 _ _ ts241_sum ts241_parity
  apply product_cons_b t242 tb242 ts242 _ _ ts242_sum ts242_parity
  apply product_cons_b t243 tb243 ts243 _ _ ts243_sum ts243_parity
  apply product_cons_b t244 tb244 ts244 _ _ ts244_sum ts244_parity
  apply product_cons_b t245 tb245 ts245 _ _ ts245_sum ts245_parity
  apply product_cons_b t246 tb246 ts246 _ _ ts246_sum ts246_parity
  apply product_cons_b t247 tb247 ts247 _ _ ts247_sum ts247_parity
  apply product_cons_b t248 tb248 ts248 _ _ ts248_sum ts248_parity
  apply product_cons_b t249 tb249 ts249 _ _ ts249_sum ts249_parity
  apply product_cons_b t250 tb250 ts250 _ _ ts250_sum ts250_parity
  apply product_cons_b t251 tb251 ts251 _ _ ts251_sum ts251_parity
  apply product_cons_b t252 tb252 ts252 _ _ ts252_sum ts252_parity
  apply product_cons_b t253 tb253 ts253 _ _ ts253_sum ts253_parity
  apply product_cons_b t254 tb254 ts254 _ _ ts254_sum ts254_parity
  apply product_cons_b t255 tb255 ts255 _ _ ts255_sum ts255_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d192 da192 ds192 _ _ ds192_sum ds192_parity
  apply product_cons_a d193 da193 ds193 _ _ ds193_sum ds193_parity
  apply product_cons_a d194 da194 ds194 _ _ ds194_sum ds194_parity
  apply product_cons_a d195 da195 ds195 _ _ ds195_sum ds195_parity
  apply product_cons_a d196 da196 ds196 _ _ ds196_sum ds196_parity
  apply product_cons_a d197 da197 ds197 _ _ ds197_sum ds197_parity
  apply product_cons_a d198 da198 ds198 _ _ ds198_sum ds198_parity
  apply product_cons_a d199 da199 ds199 _ _ ds199_sum ds199_parity
  apply product_cons_a d200 da200 ds200 _ _ ds200_sum ds200_parity
  apply product_cons_a d201 da201 ds201 _ _ ds201_sum ds201_parity
  apply product_cons_a d202 da202 ds202 _ _ ds202_sum ds202_parity
  apply product_cons_a d203 da203 ds203 _ _ ds203_sum ds203_parity
  apply product_cons_a d204 da204 ds204 _ _ ds204_sum ds204_parity
  apply product_cons_a d205 da205 ds205 _ _ ds205_sum ds205_parity
  apply product_cons_a d206 da206 ds206 _ _ ds206_sum ds206_parity
  apply product_cons_a d207 da207 ds207 _ _ ds207_sum ds207_parity
  apply product_cons_a d208 da208 ds208 _ _ ds208_sum ds208_parity
  apply product_cons_a d209 da209 ds209 _ _ ds209_sum ds209_parity
  apply product_cons_a d210 da210 ds210 _ _ ds210_sum ds210_parity
  apply product_cons_a d211 da211 ds211 _ _ ds211_sum ds211_parity
  apply product_cons_a d212 da212 ds212 _ _ ds212_sum ds212_parity
  apply product_cons_a d213 da213 ds213 _ _ ds213_sum ds213_parity
  apply product_cons_a d214 da214 ds214 _ _ ds214_sum ds214_parity
  apply product_cons_a d215 da215 ds215 _ _ ds215_sum ds215_parity
  apply product_cons_a d216 da216 ds216 _ _ ds216_sum ds216_parity
  apply product_cons_a d217 da217 ds217 _ _ ds217_sum ds217_parity
  apply product_cons_a d218 da218 ds218 _ _ ds218_sum ds218_parity
  apply product_cons_a d219 da219 ds219 _ _ ds219_sum ds219_parity
  apply product_cons_a d220 da220 ds220 _ _ ds220_sum ds220_parity
  apply product_cons_a d221 da221 ds221 _ _ ds221_sum ds221_parity
  apply product_cons_a d222 da222 ds222 _ _ ds222_sum ds222_parity
  apply product_cons_a d223 da223 ds223 _ _ ds223_sum ds223_parity
  apply product_cons_a d224 da224 ds224 _ _ ds224_sum ds224_parity
  apply product_cons_a d225 da225 ds225 _ _ ds225_sum ds225_parity
  apply product_cons_a d226 da226 ds226 _ _ ds226_sum ds226_parity
  apply product_cons_a d227 da227 ds227 _ _ ds227_sum ds227_parity
  apply product_cons_a d228 da228 ds228 _ _ ds228_sum ds228_parity
  apply product_cons_a d229 da229 ds229 _ _ ds229_sum ds229_parity
  apply product_cons_a d230 da230 ds230 _ _ ds230_sum ds230_parity
  apply product_cons_a d231 da231 ds231 _ _ ds231_sum ds231_parity
  apply product_cons_a d232 da232 ds232 _ _ ds232_sum ds232_parity
  apply product_cons_a d233 da233 ds233 _ _ ds233_sum ds233_parity
  apply product_cons_a d234 da234 ds234 _ _ ds234_sum ds234_parity
  apply product_cons_a d235 da235 ds235 _ _ ds235_sum ds235_parity
  apply product_cons_a d236 da236 ds236 _ _ ds236_sum ds236_parity
  apply product_cons_a d237 da237 ds237 _ _ ds237_sum ds237_parity
  apply product_cons_a d238 da238 ds238 _ _ ds238_sum ds238_parity
  apply product_cons_a d239 da239 ds239 _ _ ds239_sum ds239_parity
  apply product_cons_a d240 da240 ds240 _ _ ds240_sum ds240_parity
  apply product_cons_a d241 da241 ds241 _ _ ds241_sum ds241_parity
  apply product_cons_a d242 da242 ds242 _ _ ds242_sum ds242_parity
  apply product_cons_a d243 da243 ds243 _ _ ds243_sum ds243_parity
  apply product_cons_a d244 da244 ds244 _ _ ds244_sum ds244_parity
  apply product_cons_a d245 da245 ds245 _ _ ds245_sum ds245_parity
  apply product_cons_a d246 da246 ds246 _ _ ds246_sum ds246_parity
  apply product_cons_a d247 da247 ds247 _ _ ds247_sum ds247_parity
  apply product_cons_a d248 da248 ds248 _ _ ds248_sum ds248_parity
  apply product_cons_a d249 da249 ds249 _ _ ds249_sum ds249_parity
  apply product_cons_a d250 da250 ds250 _ _ ds250_sum ds250_parity
  apply product_cons_a d251 da251 ds251 _ _ ds251_sum ds251_parity
  apply product_cons_a d252 da252 ds252 _ _ ds252_sum ds252_parity
  apply product_cons_a d253 da253 ds253 _ _ ds253_sum ds253_parity
  apply product_cons_a d254 da254 ds254 _ _ ds254_sum ds254_parity
  apply product_cons_a d255 da255 ds255 _ _ ds255_sum ds255_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 192).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 192).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 192).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 192).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 192).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 192).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 192).take 64) RightCertificate.wideSecond ((tbRows.drop 192).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 192).take 64) RightCertificate.wideFirst ((daRows.drop 192).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block03
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
