module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar06

/-!
# Exact product checks on rows 384 through 447

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block06

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t384 tb384 ts384 _ _ ts384_sum ts384_parity
  apply product_cons_b t385 tb385 ts385 _ _ ts385_sum ts385_parity
  apply product_cons_b t386 tb386 ts386 _ _ ts386_sum ts386_parity
  apply product_cons_b t387 tb387 ts387 _ _ ts387_sum ts387_parity
  apply product_cons_b t388 tb388 ts388 _ _ ts388_sum ts388_parity
  apply product_cons_b t389 tb389 ts389 _ _ ts389_sum ts389_parity
  apply product_cons_b t390 tb390 ts390 _ _ ts390_sum ts390_parity
  apply product_cons_b t391 tb391 ts391 _ _ ts391_sum ts391_parity
  apply product_cons_b t392 tb392 ts392 _ _ ts392_sum ts392_parity
  apply product_cons_b t393 tb393 ts393 _ _ ts393_sum ts393_parity
  apply product_cons_b t394 tb394 ts394 _ _ ts394_sum ts394_parity
  apply product_cons_b t395 tb395 ts395 _ _ ts395_sum ts395_parity
  apply product_cons_b t396 tb396 ts396 _ _ ts396_sum ts396_parity
  apply product_cons_b t397 tb397 ts397 _ _ ts397_sum ts397_parity
  apply product_cons_b t398 tb398 ts398 _ _ ts398_sum ts398_parity
  apply product_cons_b t399 tb399 ts399 _ _ ts399_sum ts399_parity
  apply product_cons_b t400 tb400 ts400 _ _ ts400_sum ts400_parity
  apply product_cons_b t401 tb401 ts401 _ _ ts401_sum ts401_parity
  apply product_cons_b t402 tb402 ts402 _ _ ts402_sum ts402_parity
  apply product_cons_b t403 tb403 ts403 _ _ ts403_sum ts403_parity
  apply product_cons_b t404 tb404 ts404 _ _ ts404_sum ts404_parity
  apply product_cons_b t405 tb405 ts405 _ _ ts405_sum ts405_parity
  apply product_cons_b t406 tb406 ts406 _ _ ts406_sum ts406_parity
  apply product_cons_b t407 tb407 ts407 _ _ ts407_sum ts407_parity
  apply product_cons_b t408 tb408 ts408 _ _ ts408_sum ts408_parity
  apply product_cons_b t409 tb409 ts409 _ _ ts409_sum ts409_parity
  apply product_cons_b t410 tb410 ts410 _ _ ts410_sum ts410_parity
  apply product_cons_b t411 tb411 ts411 _ _ ts411_sum ts411_parity
  apply product_cons_b t412 tb412 ts412 _ _ ts412_sum ts412_parity
  apply product_cons_b t413 tb413 ts413 _ _ ts413_sum ts413_parity
  apply product_cons_b t414 tb414 ts414 _ _ ts414_sum ts414_parity
  apply product_cons_b t415 tb415 ts415 _ _ ts415_sum ts415_parity
  apply product_cons_b t416 tb416 ts416 _ _ ts416_sum ts416_parity
  apply product_cons_b t417 tb417 ts417 _ _ ts417_sum ts417_parity
  apply product_cons_b t418 tb418 ts418 _ _ ts418_sum ts418_parity
  apply product_cons_b t419 tb419 ts419 _ _ ts419_sum ts419_parity
  apply product_cons_b t420 tb420 ts420 _ _ ts420_sum ts420_parity
  apply product_cons_b t421 tb421 ts421 _ _ ts421_sum ts421_parity
  apply product_cons_b t422 tb422 ts422 _ _ ts422_sum ts422_parity
  apply product_cons_b t423 tb423 ts423 _ _ ts423_sum ts423_parity
  apply product_cons_b t424 tb424 ts424 _ _ ts424_sum ts424_parity
  apply product_cons_b t425 tb425 ts425 _ _ ts425_sum ts425_parity
  apply product_cons_b t426 tb426 ts426 _ _ ts426_sum ts426_parity
  apply product_cons_b t427 tb427 ts427 _ _ ts427_sum ts427_parity
  apply product_cons_b t428 tb428 ts428 _ _ ts428_sum ts428_parity
  apply product_cons_b t429 tb429 ts429 _ _ ts429_sum ts429_parity
  apply product_cons_b t430 tb430 ts430 _ _ ts430_sum ts430_parity
  apply product_cons_b t431 tb431 ts431 _ _ ts431_sum ts431_parity
  apply product_cons_b t432 tb432 ts432 _ _ ts432_sum ts432_parity
  apply product_cons_b t433 tb433 ts433 _ _ ts433_sum ts433_parity
  apply product_cons_b t434 tb434 ts434 _ _ ts434_sum ts434_parity
  apply product_cons_b t435 tb435 ts435 _ _ ts435_sum ts435_parity
  apply product_cons_b t436 tb436 ts436 _ _ ts436_sum ts436_parity
  apply product_cons_b t437 tb437 ts437 _ _ ts437_sum ts437_parity
  apply product_cons_b t438 tb438 ts438 _ _ ts438_sum ts438_parity
  apply product_cons_b t439 tb439 ts439 _ _ ts439_sum ts439_parity
  apply product_cons_b t440 tb440 ts440 _ _ ts440_sum ts440_parity
  apply product_cons_b t441 tb441 ts441 _ _ ts441_sum ts441_parity
  apply product_cons_b t442 tb442 ts442 _ _ ts442_sum ts442_parity
  apply product_cons_b t443 tb443 ts443 _ _ ts443_sum ts443_parity
  apply product_cons_b t444 tb444 ts444 _ _ ts444_sum ts444_parity
  apply product_cons_b t445 tb445 ts445 _ _ ts445_sum ts445_parity
  apply product_cons_b t446 tb446 ts446 _ _ ts446_sum ts446_parity
  apply product_cons_b t447 tb447 ts447 _ _ ts447_sum ts447_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d384 da384 ds384 _ _ ds384_sum ds384_parity
  apply product_cons_a d385 da385 ds385 _ _ ds385_sum ds385_parity
  apply product_cons_a d386 da386 ds386 _ _ ds386_sum ds386_parity
  apply product_cons_a d387 da387 ds387 _ _ ds387_sum ds387_parity
  apply product_cons_a d388 da388 ds388 _ _ ds388_sum ds388_parity
  apply product_cons_a d389 da389 ds389 _ _ ds389_sum ds389_parity
  apply product_cons_a d390 da390 ds390 _ _ ds390_sum ds390_parity
  apply product_cons_a d391 da391 ds391 _ _ ds391_sum ds391_parity
  apply product_cons_a d392 da392 ds392 _ _ ds392_sum ds392_parity
  apply product_cons_a d393 da393 ds393 _ _ ds393_sum ds393_parity
  apply product_cons_a d394 da394 ds394 _ _ ds394_sum ds394_parity
  apply product_cons_a d395 da395 ds395 _ _ ds395_sum ds395_parity
  apply product_cons_a d396 da396 ds396 _ _ ds396_sum ds396_parity
  apply product_cons_a d397 da397 ds397 _ _ ds397_sum ds397_parity
  apply product_cons_a d398 da398 ds398 _ _ ds398_sum ds398_parity
  apply product_cons_a d399 da399 ds399 _ _ ds399_sum ds399_parity
  apply product_cons_a d400 da400 ds400 _ _ ds400_sum ds400_parity
  apply product_cons_a d401 da401 ds401 _ _ ds401_sum ds401_parity
  apply product_cons_a d402 da402 ds402 _ _ ds402_sum ds402_parity
  apply product_cons_a d403 da403 ds403 _ _ ds403_sum ds403_parity
  apply product_cons_a d404 da404 ds404 _ _ ds404_sum ds404_parity
  apply product_cons_a d405 da405 ds405 _ _ ds405_sum ds405_parity
  apply product_cons_a d406 da406 ds406 _ _ ds406_sum ds406_parity
  apply product_cons_a d407 da407 ds407 _ _ ds407_sum ds407_parity
  apply product_cons_a d408 da408 ds408 _ _ ds408_sum ds408_parity
  apply product_cons_a d409 da409 ds409 _ _ ds409_sum ds409_parity
  apply product_cons_a d410 da410 ds410 _ _ ds410_sum ds410_parity
  apply product_cons_a d411 da411 ds411 _ _ ds411_sum ds411_parity
  apply product_cons_a d412 da412 ds412 _ _ ds412_sum ds412_parity
  apply product_cons_a d413 da413 ds413 _ _ ds413_sum ds413_parity
  apply product_cons_a d414 da414 ds414 _ _ ds414_sum ds414_parity
  apply product_cons_a d415 da415 ds415 _ _ ds415_sum ds415_parity
  apply product_cons_a d416 da416 ds416 _ _ ds416_sum ds416_parity
  apply product_cons_a d417 da417 ds417 _ _ ds417_sum ds417_parity
  apply product_cons_a d418 da418 ds418 _ _ ds418_sum ds418_parity
  apply product_cons_a d419 da419 ds419 _ _ ds419_sum ds419_parity
  apply product_cons_a d420 da420 ds420 _ _ ds420_sum ds420_parity
  apply product_cons_a d421 da421 ds421 _ _ ds421_sum ds421_parity
  apply product_cons_a d422 da422 ds422 _ _ ds422_sum ds422_parity
  apply product_cons_a d423 da423 ds423 _ _ ds423_sum ds423_parity
  apply product_cons_a d424 da424 ds424 _ _ ds424_sum ds424_parity
  apply product_cons_a d425 da425 ds425 _ _ ds425_sum ds425_parity
  apply product_cons_a d426 da426 ds426 _ _ ds426_sum ds426_parity
  apply product_cons_a d427 da427 ds427 _ _ ds427_sum ds427_parity
  apply product_cons_a d428 da428 ds428 _ _ ds428_sum ds428_parity
  apply product_cons_a d429 da429 ds429 _ _ ds429_sum ds429_parity
  apply product_cons_a d430 da430 ds430 _ _ ds430_sum ds430_parity
  apply product_cons_a d431 da431 ds431 _ _ ds431_sum ds431_parity
  apply product_cons_a d432 da432 ds432 _ _ ds432_sum ds432_parity
  apply product_cons_a d433 da433 ds433 _ _ ds433_sum ds433_parity
  apply product_cons_a d434 da434 ds434 _ _ ds434_sum ds434_parity
  apply product_cons_a d435 da435 ds435 _ _ ds435_sum ds435_parity
  apply product_cons_a d436 da436 ds436 _ _ ds436_sum ds436_parity
  apply product_cons_a d437 da437 ds437 _ _ ds437_sum ds437_parity
  apply product_cons_a d438 da438 ds438 _ _ ds438_sum ds438_parity
  apply product_cons_a d439 da439 ds439 _ _ ds439_sum ds439_parity
  apply product_cons_a d440 da440 ds440 _ _ ds440_sum ds440_parity
  apply product_cons_a d441 da441 ds441 _ _ ds441_sum ds441_parity
  apply product_cons_a d442 da442 ds442 _ _ ds442_sum ds442_parity
  apply product_cons_a d443 da443 ds443 _ _ ds443_sum ds443_parity
  apply product_cons_a d444 da444 ds444 _ _ ds444_sum ds444_parity
  apply product_cons_a d445 da445 ds445 _ _ ds445_sum ds445_parity
  apply product_cons_a d446 da446 ds446 _ _ ds446_sum ds446_parity
  apply product_cons_a d447 da447 ds447 _ _ ds447_sum ds447_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 384).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 384).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 384).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 384).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 384).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 384).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 384).take 64) RightCertificate.wideSecond ((tbRows.drop 384).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 384).take 64) RightCertificate.wideFirst ((daRows.drop 384).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block06
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
