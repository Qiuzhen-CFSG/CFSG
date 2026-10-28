module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar05

/-!
# Exact product checks on rows 320 through 383

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block05

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t320 tb320 ts320 _ _ ts320_sum ts320_parity
  apply product_cons_b t321 tb321 ts321 _ _ ts321_sum ts321_parity
  apply product_cons_b t322 tb322 ts322 _ _ ts322_sum ts322_parity
  apply product_cons_b t323 tb323 ts323 _ _ ts323_sum ts323_parity
  apply product_cons_b t324 tb324 ts324 _ _ ts324_sum ts324_parity
  apply product_cons_b t325 tb325 ts325 _ _ ts325_sum ts325_parity
  apply product_cons_b t326 tb326 ts326 _ _ ts326_sum ts326_parity
  apply product_cons_b t327 tb327 ts327 _ _ ts327_sum ts327_parity
  apply product_cons_b t328 tb328 ts328 _ _ ts328_sum ts328_parity
  apply product_cons_b t329 tb329 ts329 _ _ ts329_sum ts329_parity
  apply product_cons_b t330 tb330 ts330 _ _ ts330_sum ts330_parity
  apply product_cons_b t331 tb331 ts331 _ _ ts331_sum ts331_parity
  apply product_cons_b t332 tb332 ts332 _ _ ts332_sum ts332_parity
  apply product_cons_b t333 tb333 ts333 _ _ ts333_sum ts333_parity
  apply product_cons_b t334 tb334 ts334 _ _ ts334_sum ts334_parity
  apply product_cons_b t335 tb335 ts335 _ _ ts335_sum ts335_parity
  apply product_cons_b t336 tb336 ts336 _ _ ts336_sum ts336_parity
  apply product_cons_b t337 tb337 ts337 _ _ ts337_sum ts337_parity
  apply product_cons_b t338 tb338 ts338 _ _ ts338_sum ts338_parity
  apply product_cons_b t339 tb339 ts339 _ _ ts339_sum ts339_parity
  apply product_cons_b t340 tb340 ts340 _ _ ts340_sum ts340_parity
  apply product_cons_b t341 tb341 ts341 _ _ ts341_sum ts341_parity
  apply product_cons_b t342 tb342 ts342 _ _ ts342_sum ts342_parity
  apply product_cons_b t343 tb343 ts343 _ _ ts343_sum ts343_parity
  apply product_cons_b t344 tb344 ts344 _ _ ts344_sum ts344_parity
  apply product_cons_b t345 tb345 ts345 _ _ ts345_sum ts345_parity
  apply product_cons_b t346 tb346 ts346 _ _ ts346_sum ts346_parity
  apply product_cons_b t347 tb347 ts347 _ _ ts347_sum ts347_parity
  apply product_cons_b t348 tb348 ts348 _ _ ts348_sum ts348_parity
  apply product_cons_b t349 tb349 ts349 _ _ ts349_sum ts349_parity
  apply product_cons_b t350 tb350 ts350 _ _ ts350_sum ts350_parity
  apply product_cons_b t351 tb351 ts351 _ _ ts351_sum ts351_parity
  apply product_cons_b t352 tb352 ts352 _ _ ts352_sum ts352_parity
  apply product_cons_b t353 tb353 ts353 _ _ ts353_sum ts353_parity
  apply product_cons_b t354 tb354 ts354 _ _ ts354_sum ts354_parity
  apply product_cons_b t355 tb355 ts355 _ _ ts355_sum ts355_parity
  apply product_cons_b t356 tb356 ts356 _ _ ts356_sum ts356_parity
  apply product_cons_b t357 tb357 ts357 _ _ ts357_sum ts357_parity
  apply product_cons_b t358 tb358 ts358 _ _ ts358_sum ts358_parity
  apply product_cons_b t359 tb359 ts359 _ _ ts359_sum ts359_parity
  apply product_cons_b t360 tb360 ts360 _ _ ts360_sum ts360_parity
  apply product_cons_b t361 tb361 ts361 _ _ ts361_sum ts361_parity
  apply product_cons_b t362 tb362 ts362 _ _ ts362_sum ts362_parity
  apply product_cons_b t363 tb363 ts363 _ _ ts363_sum ts363_parity
  apply product_cons_b t364 tb364 ts364 _ _ ts364_sum ts364_parity
  apply product_cons_b t365 tb365 ts365 _ _ ts365_sum ts365_parity
  apply product_cons_b t366 tb366 ts366 _ _ ts366_sum ts366_parity
  apply product_cons_b t367 tb367 ts367 _ _ ts367_sum ts367_parity
  apply product_cons_b t368 tb368 ts368 _ _ ts368_sum ts368_parity
  apply product_cons_b t369 tb369 ts369 _ _ ts369_sum ts369_parity
  apply product_cons_b t370 tb370 ts370 _ _ ts370_sum ts370_parity
  apply product_cons_b t371 tb371 ts371 _ _ ts371_sum ts371_parity
  apply product_cons_b t372 tb372 ts372 _ _ ts372_sum ts372_parity
  apply product_cons_b t373 tb373 ts373 _ _ ts373_sum ts373_parity
  apply product_cons_b t374 tb374 ts374 _ _ ts374_sum ts374_parity
  apply product_cons_b t375 tb375 ts375 _ _ ts375_sum ts375_parity
  apply product_cons_b t376 tb376 ts376 _ _ ts376_sum ts376_parity
  apply product_cons_b t377 tb377 ts377 _ _ ts377_sum ts377_parity
  apply product_cons_b t378 tb378 ts378 _ _ ts378_sum ts378_parity
  apply product_cons_b t379 tb379 ts379 _ _ ts379_sum ts379_parity
  apply product_cons_b t380 tb380 ts380 _ _ ts380_sum ts380_parity
  apply product_cons_b t381 tb381 ts381 _ _ ts381_sum ts381_parity
  apply product_cons_b t382 tb382 ts382 _ _ ts382_sum ts382_parity
  apply product_cons_b t383 tb383 ts383 _ _ ts383_sum ts383_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d320 da320 ds320 _ _ ds320_sum ds320_parity
  apply product_cons_a d321 da321 ds321 _ _ ds321_sum ds321_parity
  apply product_cons_a d322 da322 ds322 _ _ ds322_sum ds322_parity
  apply product_cons_a d323 da323 ds323 _ _ ds323_sum ds323_parity
  apply product_cons_a d324 da324 ds324 _ _ ds324_sum ds324_parity
  apply product_cons_a d325 da325 ds325 _ _ ds325_sum ds325_parity
  apply product_cons_a d326 da326 ds326 _ _ ds326_sum ds326_parity
  apply product_cons_a d327 da327 ds327 _ _ ds327_sum ds327_parity
  apply product_cons_a d328 da328 ds328 _ _ ds328_sum ds328_parity
  apply product_cons_a d329 da329 ds329 _ _ ds329_sum ds329_parity
  apply product_cons_a d330 da330 ds330 _ _ ds330_sum ds330_parity
  apply product_cons_a d331 da331 ds331 _ _ ds331_sum ds331_parity
  apply product_cons_a d332 da332 ds332 _ _ ds332_sum ds332_parity
  apply product_cons_a d333 da333 ds333 _ _ ds333_sum ds333_parity
  apply product_cons_a d334 da334 ds334 _ _ ds334_sum ds334_parity
  apply product_cons_a d335 da335 ds335 _ _ ds335_sum ds335_parity
  apply product_cons_a d336 da336 ds336 _ _ ds336_sum ds336_parity
  apply product_cons_a d337 da337 ds337 _ _ ds337_sum ds337_parity
  apply product_cons_a d338 da338 ds338 _ _ ds338_sum ds338_parity
  apply product_cons_a d339 da339 ds339 _ _ ds339_sum ds339_parity
  apply product_cons_a d340 da340 ds340 _ _ ds340_sum ds340_parity
  apply product_cons_a d341 da341 ds341 _ _ ds341_sum ds341_parity
  apply product_cons_a d342 da342 ds342 _ _ ds342_sum ds342_parity
  apply product_cons_a d343 da343 ds343 _ _ ds343_sum ds343_parity
  apply product_cons_a d344 da344 ds344 _ _ ds344_sum ds344_parity
  apply product_cons_a d345 da345 ds345 _ _ ds345_sum ds345_parity
  apply product_cons_a d346 da346 ds346 _ _ ds346_sum ds346_parity
  apply product_cons_a d347 da347 ds347 _ _ ds347_sum ds347_parity
  apply product_cons_a d348 da348 ds348 _ _ ds348_sum ds348_parity
  apply product_cons_a d349 da349 ds349 _ _ ds349_sum ds349_parity
  apply product_cons_a d350 da350 ds350 _ _ ds350_sum ds350_parity
  apply product_cons_a d351 da351 ds351 _ _ ds351_sum ds351_parity
  apply product_cons_a d352 da352 ds352 _ _ ds352_sum ds352_parity
  apply product_cons_a d353 da353 ds353 _ _ ds353_sum ds353_parity
  apply product_cons_a d354 da354 ds354 _ _ ds354_sum ds354_parity
  apply product_cons_a d355 da355 ds355 _ _ ds355_sum ds355_parity
  apply product_cons_a d356 da356 ds356 _ _ ds356_sum ds356_parity
  apply product_cons_a d357 da357 ds357 _ _ ds357_sum ds357_parity
  apply product_cons_a d358 da358 ds358 _ _ ds358_sum ds358_parity
  apply product_cons_a d359 da359 ds359 _ _ ds359_sum ds359_parity
  apply product_cons_a d360 da360 ds360 _ _ ds360_sum ds360_parity
  apply product_cons_a d361 da361 ds361 _ _ ds361_sum ds361_parity
  apply product_cons_a d362 da362 ds362 _ _ ds362_sum ds362_parity
  apply product_cons_a d363 da363 ds363 _ _ ds363_sum ds363_parity
  apply product_cons_a d364 da364 ds364 _ _ ds364_sum ds364_parity
  apply product_cons_a d365 da365 ds365 _ _ ds365_sum ds365_parity
  apply product_cons_a d366 da366 ds366 _ _ ds366_sum ds366_parity
  apply product_cons_a d367 da367 ds367 _ _ ds367_sum ds367_parity
  apply product_cons_a d368 da368 ds368 _ _ ds368_sum ds368_parity
  apply product_cons_a d369 da369 ds369 _ _ ds369_sum ds369_parity
  apply product_cons_a d370 da370 ds370 _ _ ds370_sum ds370_parity
  apply product_cons_a d371 da371 ds371 _ _ ds371_sum ds371_parity
  apply product_cons_a d372 da372 ds372 _ _ ds372_sum ds372_parity
  apply product_cons_a d373 da373 ds373 _ _ ds373_sum ds373_parity
  apply product_cons_a d374 da374 ds374 _ _ ds374_sum ds374_parity
  apply product_cons_a d375 da375 ds375 _ _ ds375_sum ds375_parity
  apply product_cons_a d376 da376 ds376 _ _ ds376_sum ds376_parity
  apply product_cons_a d377 da377 ds377 _ _ ds377_sum ds377_parity
  apply product_cons_a d378 da378 ds378 _ _ ds378_sum ds378_parity
  apply product_cons_a d379 da379 ds379 _ _ ds379_sum ds379_parity
  apply product_cons_a d380 da380 ds380 _ _ ds380_sum ds380_parity
  apply product_cons_a d381 da381 ds381 _ _ ds381_sum ds381_parity
  apply product_cons_a d382 da382 ds382 _ _ ds382_sum ds382_parity
  apply product_cons_a d383 da383 ds383 _ _ ds383_sum ds383_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 320).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 320).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 320).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 320).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 320).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 320).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 320).take 64) RightCertificate.wideSecond ((tbRows.drop 320).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 320).take 64) RightCertificate.wideFirst ((daRows.drop 320).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block05
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
