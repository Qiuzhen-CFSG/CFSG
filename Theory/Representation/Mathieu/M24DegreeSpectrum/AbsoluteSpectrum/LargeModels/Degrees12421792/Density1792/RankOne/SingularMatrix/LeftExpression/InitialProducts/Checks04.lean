module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar04

/-!
# Exact product checks on rows 256 through 319

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block04

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t256 tb256 ts256 _ _ ts256_sum ts256_parity
  apply product_cons_b t257 tb257 ts257 _ _ ts257_sum ts257_parity
  apply product_cons_b t258 tb258 ts258 _ _ ts258_sum ts258_parity
  apply product_cons_b t259 tb259 ts259 _ _ ts259_sum ts259_parity
  apply product_cons_b t260 tb260 ts260 _ _ ts260_sum ts260_parity
  apply product_cons_b t261 tb261 ts261 _ _ ts261_sum ts261_parity
  apply product_cons_b t262 tb262 ts262 _ _ ts262_sum ts262_parity
  apply product_cons_b t263 tb263 ts263 _ _ ts263_sum ts263_parity
  apply product_cons_b t264 tb264 ts264 _ _ ts264_sum ts264_parity
  apply product_cons_b t265 tb265 ts265 _ _ ts265_sum ts265_parity
  apply product_cons_b t266 tb266 ts266 _ _ ts266_sum ts266_parity
  apply product_cons_b t267 tb267 ts267 _ _ ts267_sum ts267_parity
  apply product_cons_b t268 tb268 ts268 _ _ ts268_sum ts268_parity
  apply product_cons_b t269 tb269 ts269 _ _ ts269_sum ts269_parity
  apply product_cons_b t270 tb270 ts270 _ _ ts270_sum ts270_parity
  apply product_cons_b t271 tb271 ts271 _ _ ts271_sum ts271_parity
  apply product_cons_b t272 tb272 ts272 _ _ ts272_sum ts272_parity
  apply product_cons_b t273 tb273 ts273 _ _ ts273_sum ts273_parity
  apply product_cons_b t274 tb274 ts274 _ _ ts274_sum ts274_parity
  apply product_cons_b t275 tb275 ts275 _ _ ts275_sum ts275_parity
  apply product_cons_b t276 tb276 ts276 _ _ ts276_sum ts276_parity
  apply product_cons_b t277 tb277 ts277 _ _ ts277_sum ts277_parity
  apply product_cons_b t278 tb278 ts278 _ _ ts278_sum ts278_parity
  apply product_cons_b t279 tb279 ts279 _ _ ts279_sum ts279_parity
  apply product_cons_b t280 tb280 ts280 _ _ ts280_sum ts280_parity
  apply product_cons_b t281 tb281 ts281 _ _ ts281_sum ts281_parity
  apply product_cons_b t282 tb282 ts282 _ _ ts282_sum ts282_parity
  apply product_cons_b t283 tb283 ts283 _ _ ts283_sum ts283_parity
  apply product_cons_b t284 tb284 ts284 _ _ ts284_sum ts284_parity
  apply product_cons_b t285 tb285 ts285 _ _ ts285_sum ts285_parity
  apply product_cons_b t286 tb286 ts286 _ _ ts286_sum ts286_parity
  apply product_cons_b t287 tb287 ts287 _ _ ts287_sum ts287_parity
  apply product_cons_b t288 tb288 ts288 _ _ ts288_sum ts288_parity
  apply product_cons_b t289 tb289 ts289 _ _ ts289_sum ts289_parity
  apply product_cons_b t290 tb290 ts290 _ _ ts290_sum ts290_parity
  apply product_cons_b t291 tb291 ts291 _ _ ts291_sum ts291_parity
  apply product_cons_b t292 tb292 ts292 _ _ ts292_sum ts292_parity
  apply product_cons_b t293 tb293 ts293 _ _ ts293_sum ts293_parity
  apply product_cons_b t294 tb294 ts294 _ _ ts294_sum ts294_parity
  apply product_cons_b t295 tb295 ts295 _ _ ts295_sum ts295_parity
  apply product_cons_b t296 tb296 ts296 _ _ ts296_sum ts296_parity
  apply product_cons_b t297 tb297 ts297 _ _ ts297_sum ts297_parity
  apply product_cons_b t298 tb298 ts298 _ _ ts298_sum ts298_parity
  apply product_cons_b t299 tb299 ts299 _ _ ts299_sum ts299_parity
  apply product_cons_b t300 tb300 ts300 _ _ ts300_sum ts300_parity
  apply product_cons_b t301 tb301 ts301 _ _ ts301_sum ts301_parity
  apply product_cons_b t302 tb302 ts302 _ _ ts302_sum ts302_parity
  apply product_cons_b t303 tb303 ts303 _ _ ts303_sum ts303_parity
  apply product_cons_b t304 tb304 ts304 _ _ ts304_sum ts304_parity
  apply product_cons_b t305 tb305 ts305 _ _ ts305_sum ts305_parity
  apply product_cons_b t306 tb306 ts306 _ _ ts306_sum ts306_parity
  apply product_cons_b t307 tb307 ts307 _ _ ts307_sum ts307_parity
  apply product_cons_b t308 tb308 ts308 _ _ ts308_sum ts308_parity
  apply product_cons_b t309 tb309 ts309 _ _ ts309_sum ts309_parity
  apply product_cons_b t310 tb310 ts310 _ _ ts310_sum ts310_parity
  apply product_cons_b t311 tb311 ts311 _ _ ts311_sum ts311_parity
  apply product_cons_b t312 tb312 ts312 _ _ ts312_sum ts312_parity
  apply product_cons_b t313 tb313 ts313 _ _ ts313_sum ts313_parity
  apply product_cons_b t314 tb314 ts314 _ _ ts314_sum ts314_parity
  apply product_cons_b t315 tb315 ts315 _ _ ts315_sum ts315_parity
  apply product_cons_b t316 tb316 ts316 _ _ ts316_sum ts316_parity
  apply product_cons_b t317 tb317 ts317 _ _ ts317_sum ts317_parity
  apply product_cons_b t318 tb318 ts318 _ _ ts318_sum ts318_parity
  apply product_cons_b t319 tb319 ts319 _ _ ts319_sum ts319_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d256 da256 ds256 _ _ ds256_sum ds256_parity
  apply product_cons_a d257 da257 ds257 _ _ ds257_sum ds257_parity
  apply product_cons_a d258 da258 ds258 _ _ ds258_sum ds258_parity
  apply product_cons_a d259 da259 ds259 _ _ ds259_sum ds259_parity
  apply product_cons_a d260 da260 ds260 _ _ ds260_sum ds260_parity
  apply product_cons_a d261 da261 ds261 _ _ ds261_sum ds261_parity
  apply product_cons_a d262 da262 ds262 _ _ ds262_sum ds262_parity
  apply product_cons_a d263 da263 ds263 _ _ ds263_sum ds263_parity
  apply product_cons_a d264 da264 ds264 _ _ ds264_sum ds264_parity
  apply product_cons_a d265 da265 ds265 _ _ ds265_sum ds265_parity
  apply product_cons_a d266 da266 ds266 _ _ ds266_sum ds266_parity
  apply product_cons_a d267 da267 ds267 _ _ ds267_sum ds267_parity
  apply product_cons_a d268 da268 ds268 _ _ ds268_sum ds268_parity
  apply product_cons_a d269 da269 ds269 _ _ ds269_sum ds269_parity
  apply product_cons_a d270 da270 ds270 _ _ ds270_sum ds270_parity
  apply product_cons_a d271 da271 ds271 _ _ ds271_sum ds271_parity
  apply product_cons_a d272 da272 ds272 _ _ ds272_sum ds272_parity
  apply product_cons_a d273 da273 ds273 _ _ ds273_sum ds273_parity
  apply product_cons_a d274 da274 ds274 _ _ ds274_sum ds274_parity
  apply product_cons_a d275 da275 ds275 _ _ ds275_sum ds275_parity
  apply product_cons_a d276 da276 ds276 _ _ ds276_sum ds276_parity
  apply product_cons_a d277 da277 ds277 _ _ ds277_sum ds277_parity
  apply product_cons_a d278 da278 ds278 _ _ ds278_sum ds278_parity
  apply product_cons_a d279 da279 ds279 _ _ ds279_sum ds279_parity
  apply product_cons_a d280 da280 ds280 _ _ ds280_sum ds280_parity
  apply product_cons_a d281 da281 ds281 _ _ ds281_sum ds281_parity
  apply product_cons_a d282 da282 ds282 _ _ ds282_sum ds282_parity
  apply product_cons_a d283 da283 ds283 _ _ ds283_sum ds283_parity
  apply product_cons_a d284 da284 ds284 _ _ ds284_sum ds284_parity
  apply product_cons_a d285 da285 ds285 _ _ ds285_sum ds285_parity
  apply product_cons_a d286 da286 ds286 _ _ ds286_sum ds286_parity
  apply product_cons_a d287 da287 ds287 _ _ ds287_sum ds287_parity
  apply product_cons_a d288 da288 ds288 _ _ ds288_sum ds288_parity
  apply product_cons_a d289 da289 ds289 _ _ ds289_sum ds289_parity
  apply product_cons_a d290 da290 ds290 _ _ ds290_sum ds290_parity
  apply product_cons_a d291 da291 ds291 _ _ ds291_sum ds291_parity
  apply product_cons_a d292 da292 ds292 _ _ ds292_sum ds292_parity
  apply product_cons_a d293 da293 ds293 _ _ ds293_sum ds293_parity
  apply product_cons_a d294 da294 ds294 _ _ ds294_sum ds294_parity
  apply product_cons_a d295 da295 ds295 _ _ ds295_sum ds295_parity
  apply product_cons_a d296 da296 ds296 _ _ ds296_sum ds296_parity
  apply product_cons_a d297 da297 ds297 _ _ ds297_sum ds297_parity
  apply product_cons_a d298 da298 ds298 _ _ ds298_sum ds298_parity
  apply product_cons_a d299 da299 ds299 _ _ ds299_sum ds299_parity
  apply product_cons_a d300 da300 ds300 _ _ ds300_sum ds300_parity
  apply product_cons_a d301 da301 ds301 _ _ ds301_sum ds301_parity
  apply product_cons_a d302 da302 ds302 _ _ ds302_sum ds302_parity
  apply product_cons_a d303 da303 ds303 _ _ ds303_sum ds303_parity
  apply product_cons_a d304 da304 ds304 _ _ ds304_sum ds304_parity
  apply product_cons_a d305 da305 ds305 _ _ ds305_sum ds305_parity
  apply product_cons_a d306 da306 ds306 _ _ ds306_sum ds306_parity
  apply product_cons_a d307 da307 ds307 _ _ ds307_sum ds307_parity
  apply product_cons_a d308 da308 ds308 _ _ ds308_sum ds308_parity
  apply product_cons_a d309 da309 ds309 _ _ ds309_sum ds309_parity
  apply product_cons_a d310 da310 ds310 _ _ ds310_sum ds310_parity
  apply product_cons_a d311 da311 ds311 _ _ ds311_sum ds311_parity
  apply product_cons_a d312 da312 ds312 _ _ ds312_sum ds312_parity
  apply product_cons_a d313 da313 ds313 _ _ ds313_sum ds313_parity
  apply product_cons_a d314 da314 ds314 _ _ ds314_sum ds314_parity
  apply product_cons_a d315 da315 ds315 _ _ ds315_sum ds315_parity
  apply product_cons_a d316 da316 ds316 _ _ ds316_sum ds316_parity
  apply product_cons_a d317 da317 ds317 _ _ ds317_sum ds317_parity
  apply product_cons_a d318 da318 ds318 _ _ ds318_sum ds318_parity
  apply product_cons_a d319 da319 ds319 _ _ ds319_sum ds319_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 256).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 256).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 256).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 256).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 256).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 256).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 256).take 64) RightCertificate.wideSecond ((tbRows.drop 256).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 256).take 64) RightCertificate.wideFirst ((daRows.drop 256).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block04
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
