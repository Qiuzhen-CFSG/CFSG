module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar20

/-!
# Exact product checks on rows 1280 through 1343

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block20

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t1280 tb1280 ts1280 _ _ ts1280_sum ts1280_parity
  apply product_cons_b t1281 tb1281 ts1281 _ _ ts1281_sum ts1281_parity
  apply product_cons_b t1282 tb1282 ts1282 _ _ ts1282_sum ts1282_parity
  apply product_cons_b t1283 tb1283 ts1283 _ _ ts1283_sum ts1283_parity
  apply product_cons_b t1284 tb1284 ts1284 _ _ ts1284_sum ts1284_parity
  apply product_cons_b t1285 tb1285 ts1285 _ _ ts1285_sum ts1285_parity
  apply product_cons_b t1286 tb1286 ts1286 _ _ ts1286_sum ts1286_parity
  apply product_cons_b t1287 tb1287 ts1287 _ _ ts1287_sum ts1287_parity
  apply product_cons_b t1288 tb1288 ts1288 _ _ ts1288_sum ts1288_parity
  apply product_cons_b t1289 tb1289 ts1289 _ _ ts1289_sum ts1289_parity
  apply product_cons_b t1290 tb1290 ts1290 _ _ ts1290_sum ts1290_parity
  apply product_cons_b t1291 tb1291 ts1291 _ _ ts1291_sum ts1291_parity
  apply product_cons_b t1292 tb1292 ts1292 _ _ ts1292_sum ts1292_parity
  apply product_cons_b t1293 tb1293 ts1293 _ _ ts1293_sum ts1293_parity
  apply product_cons_b t1294 tb1294 ts1294 _ _ ts1294_sum ts1294_parity
  apply product_cons_b t1295 tb1295 ts1295 _ _ ts1295_sum ts1295_parity
  apply product_cons_b t1296 tb1296 ts1296 _ _ ts1296_sum ts1296_parity
  apply product_cons_b t1297 tb1297 ts1297 _ _ ts1297_sum ts1297_parity
  apply product_cons_b t1298 tb1298 ts1298 _ _ ts1298_sum ts1298_parity
  apply product_cons_b t1299 tb1299 ts1299 _ _ ts1299_sum ts1299_parity
  apply product_cons_b t1300 tb1300 ts1300 _ _ ts1300_sum ts1300_parity
  apply product_cons_b t1301 tb1301 ts1301 _ _ ts1301_sum ts1301_parity
  apply product_cons_b t1302 tb1302 ts1302 _ _ ts1302_sum ts1302_parity
  apply product_cons_b t1303 tb1303 ts1303 _ _ ts1303_sum ts1303_parity
  apply product_cons_b t1304 tb1304 ts1304 _ _ ts1304_sum ts1304_parity
  apply product_cons_b t1305 tb1305 ts1305 _ _ ts1305_sum ts1305_parity
  apply product_cons_b t1306 tb1306 ts1306 _ _ ts1306_sum ts1306_parity
  apply product_cons_b t1307 tb1307 ts1307 _ _ ts1307_sum ts1307_parity
  apply product_cons_b t1308 tb1308 ts1308 _ _ ts1308_sum ts1308_parity
  apply product_cons_b t1309 tb1309 ts1309 _ _ ts1309_sum ts1309_parity
  apply product_cons_b t1310 tb1310 ts1310 _ _ ts1310_sum ts1310_parity
  apply product_cons_b t1311 tb1311 ts1311 _ _ ts1311_sum ts1311_parity
  apply product_cons_b t1312 tb1312 ts1312 _ _ ts1312_sum ts1312_parity
  apply product_cons_b t1313 tb1313 ts1313 _ _ ts1313_sum ts1313_parity
  apply product_cons_b t1314 tb1314 ts1314 _ _ ts1314_sum ts1314_parity
  apply product_cons_b t1315 tb1315 ts1315 _ _ ts1315_sum ts1315_parity
  apply product_cons_b t1316 tb1316 ts1316 _ _ ts1316_sum ts1316_parity
  apply product_cons_b t1317 tb1317 ts1317 _ _ ts1317_sum ts1317_parity
  apply product_cons_b t1318 tb1318 ts1318 _ _ ts1318_sum ts1318_parity
  apply product_cons_b t1319 tb1319 ts1319 _ _ ts1319_sum ts1319_parity
  apply product_cons_b t1320 tb1320 ts1320 _ _ ts1320_sum ts1320_parity
  apply product_cons_b t1321 tb1321 ts1321 _ _ ts1321_sum ts1321_parity
  apply product_cons_b t1322 tb1322 ts1322 _ _ ts1322_sum ts1322_parity
  apply product_cons_b t1323 tb1323 ts1323 _ _ ts1323_sum ts1323_parity
  apply product_cons_b t1324 tb1324 ts1324 _ _ ts1324_sum ts1324_parity
  apply product_cons_b t1325 tb1325 ts1325 _ _ ts1325_sum ts1325_parity
  apply product_cons_b t1326 tb1326 ts1326 _ _ ts1326_sum ts1326_parity
  apply product_cons_b t1327 tb1327 ts1327 _ _ ts1327_sum ts1327_parity
  apply product_cons_b t1328 tb1328 ts1328 _ _ ts1328_sum ts1328_parity
  apply product_cons_b t1329 tb1329 ts1329 _ _ ts1329_sum ts1329_parity
  apply product_cons_b t1330 tb1330 ts1330 _ _ ts1330_sum ts1330_parity
  apply product_cons_b t1331 tb1331 ts1331 _ _ ts1331_sum ts1331_parity
  apply product_cons_b t1332 tb1332 ts1332 _ _ ts1332_sum ts1332_parity
  apply product_cons_b t1333 tb1333 ts1333 _ _ ts1333_sum ts1333_parity
  apply product_cons_b t1334 tb1334 ts1334 _ _ ts1334_sum ts1334_parity
  apply product_cons_b t1335 tb1335 ts1335 _ _ ts1335_sum ts1335_parity
  apply product_cons_b t1336 tb1336 ts1336 _ _ ts1336_sum ts1336_parity
  apply product_cons_b t1337 tb1337 ts1337 _ _ ts1337_sum ts1337_parity
  apply product_cons_b t1338 tb1338 ts1338 _ _ ts1338_sum ts1338_parity
  apply product_cons_b t1339 tb1339 ts1339 _ _ ts1339_sum ts1339_parity
  apply product_cons_b t1340 tb1340 ts1340 _ _ ts1340_sum ts1340_parity
  apply product_cons_b t1341 tb1341 ts1341 _ _ ts1341_sum ts1341_parity
  apply product_cons_b t1342 tb1342 ts1342 _ _ ts1342_sum ts1342_parity
  apply product_cons_b t1343 tb1343 ts1343 _ _ ts1343_sum ts1343_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d1280 da1280 ds1280 _ _ ds1280_sum ds1280_parity
  apply product_cons_a d1281 da1281 ds1281 _ _ ds1281_sum ds1281_parity
  apply product_cons_a d1282 da1282 ds1282 _ _ ds1282_sum ds1282_parity
  apply product_cons_a d1283 da1283 ds1283 _ _ ds1283_sum ds1283_parity
  apply product_cons_a d1284 da1284 ds1284 _ _ ds1284_sum ds1284_parity
  apply product_cons_a d1285 da1285 ds1285 _ _ ds1285_sum ds1285_parity
  apply product_cons_a d1286 da1286 ds1286 _ _ ds1286_sum ds1286_parity
  apply product_cons_a d1287 da1287 ds1287 _ _ ds1287_sum ds1287_parity
  apply product_cons_a d1288 da1288 ds1288 _ _ ds1288_sum ds1288_parity
  apply product_cons_a d1289 da1289 ds1289 _ _ ds1289_sum ds1289_parity
  apply product_cons_a d1290 da1290 ds1290 _ _ ds1290_sum ds1290_parity
  apply product_cons_a d1291 da1291 ds1291 _ _ ds1291_sum ds1291_parity
  apply product_cons_a d1292 da1292 ds1292 _ _ ds1292_sum ds1292_parity
  apply product_cons_a d1293 da1293 ds1293 _ _ ds1293_sum ds1293_parity
  apply product_cons_a d1294 da1294 ds1294 _ _ ds1294_sum ds1294_parity
  apply product_cons_a d1295 da1295 ds1295 _ _ ds1295_sum ds1295_parity
  apply product_cons_a d1296 da1296 ds1296 _ _ ds1296_sum ds1296_parity
  apply product_cons_a d1297 da1297 ds1297 _ _ ds1297_sum ds1297_parity
  apply product_cons_a d1298 da1298 ds1298 _ _ ds1298_sum ds1298_parity
  apply product_cons_a d1299 da1299 ds1299 _ _ ds1299_sum ds1299_parity
  apply product_cons_a d1300 da1300 ds1300 _ _ ds1300_sum ds1300_parity
  apply product_cons_a d1301 da1301 ds1301 _ _ ds1301_sum ds1301_parity
  apply product_cons_a d1302 da1302 ds1302 _ _ ds1302_sum ds1302_parity
  apply product_cons_a d1303 da1303 ds1303 _ _ ds1303_sum ds1303_parity
  apply product_cons_a d1304 da1304 ds1304 _ _ ds1304_sum ds1304_parity
  apply product_cons_a d1305 da1305 ds1305 _ _ ds1305_sum ds1305_parity
  apply product_cons_a d1306 da1306 ds1306 _ _ ds1306_sum ds1306_parity
  apply product_cons_a d1307 da1307 ds1307 _ _ ds1307_sum ds1307_parity
  apply product_cons_a d1308 da1308 ds1308 _ _ ds1308_sum ds1308_parity
  apply product_cons_a d1309 da1309 ds1309 _ _ ds1309_sum ds1309_parity
  apply product_cons_a d1310 da1310 ds1310 _ _ ds1310_sum ds1310_parity
  apply product_cons_a d1311 da1311 ds1311 _ _ ds1311_sum ds1311_parity
  apply product_cons_a d1312 da1312 ds1312 _ _ ds1312_sum ds1312_parity
  apply product_cons_a d1313 da1313 ds1313 _ _ ds1313_sum ds1313_parity
  apply product_cons_a d1314 da1314 ds1314 _ _ ds1314_sum ds1314_parity
  apply product_cons_a d1315 da1315 ds1315 _ _ ds1315_sum ds1315_parity
  apply product_cons_a d1316 da1316 ds1316 _ _ ds1316_sum ds1316_parity
  apply product_cons_a d1317 da1317 ds1317 _ _ ds1317_sum ds1317_parity
  apply product_cons_a d1318 da1318 ds1318 _ _ ds1318_sum ds1318_parity
  apply product_cons_a d1319 da1319 ds1319 _ _ ds1319_sum ds1319_parity
  apply product_cons_a d1320 da1320 ds1320 _ _ ds1320_sum ds1320_parity
  apply product_cons_a d1321 da1321 ds1321 _ _ ds1321_sum ds1321_parity
  apply product_cons_a d1322 da1322 ds1322 _ _ ds1322_sum ds1322_parity
  apply product_cons_a d1323 da1323 ds1323 _ _ ds1323_sum ds1323_parity
  apply product_cons_a d1324 da1324 ds1324 _ _ ds1324_sum ds1324_parity
  apply product_cons_a d1325 da1325 ds1325 _ _ ds1325_sum ds1325_parity
  apply product_cons_a d1326 da1326 ds1326 _ _ ds1326_sum ds1326_parity
  apply product_cons_a d1327 da1327 ds1327 _ _ ds1327_sum ds1327_parity
  apply product_cons_a d1328 da1328 ds1328 _ _ ds1328_sum ds1328_parity
  apply product_cons_a d1329 da1329 ds1329 _ _ ds1329_sum ds1329_parity
  apply product_cons_a d1330 da1330 ds1330 _ _ ds1330_sum ds1330_parity
  apply product_cons_a d1331 da1331 ds1331 _ _ ds1331_sum ds1331_parity
  apply product_cons_a d1332 da1332 ds1332 _ _ ds1332_sum ds1332_parity
  apply product_cons_a d1333 da1333 ds1333 _ _ ds1333_sum ds1333_parity
  apply product_cons_a d1334 da1334 ds1334 _ _ ds1334_sum ds1334_parity
  apply product_cons_a d1335 da1335 ds1335 _ _ ds1335_sum ds1335_parity
  apply product_cons_a d1336 da1336 ds1336 _ _ ds1336_sum ds1336_parity
  apply product_cons_a d1337 da1337 ds1337 _ _ ds1337_sum ds1337_parity
  apply product_cons_a d1338 da1338 ds1338 _ _ ds1338_sum ds1338_parity
  apply product_cons_a d1339 da1339 ds1339 _ _ ds1339_sum ds1339_parity
  apply product_cons_a d1340 da1340 ds1340 _ _ ds1340_sum ds1340_parity
  apply product_cons_a d1341 da1341 ds1341 _ _ ds1341_sum ds1341_parity
  apply product_cons_a d1342 da1342 ds1342 _ _ ds1342_sum ds1342_parity
  apply product_cons_a d1343 da1343 ds1343 _ _ ds1343_sum ds1343_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 1280).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 1280).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 1280).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 1280).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 1280).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 1280).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 1280).take 64) RightCertificate.wideSecond ((tbRows.drop 1280).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 1280).take 64) RightCertificate.wideFirst ((daRows.drop 1280).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block20
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
