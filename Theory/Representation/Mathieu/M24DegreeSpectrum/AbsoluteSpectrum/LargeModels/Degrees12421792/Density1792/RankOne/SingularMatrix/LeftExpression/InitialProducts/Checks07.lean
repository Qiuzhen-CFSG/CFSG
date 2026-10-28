module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar07

/-!
# Exact product checks on rows 448 through 511

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block07

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t448 tb448 ts448 _ _ ts448_sum ts448_parity
  apply product_cons_b t449 tb449 ts449 _ _ ts449_sum ts449_parity
  apply product_cons_b t450 tb450 ts450 _ _ ts450_sum ts450_parity
  apply product_cons_b t451 tb451 ts451 _ _ ts451_sum ts451_parity
  apply product_cons_b t452 tb452 ts452 _ _ ts452_sum ts452_parity
  apply product_cons_b t453 tb453 ts453 _ _ ts453_sum ts453_parity
  apply product_cons_b t454 tb454 ts454 _ _ ts454_sum ts454_parity
  apply product_cons_b t455 tb455 ts455 _ _ ts455_sum ts455_parity
  apply product_cons_b t456 tb456 ts456 _ _ ts456_sum ts456_parity
  apply product_cons_b t457 tb457 ts457 _ _ ts457_sum ts457_parity
  apply product_cons_b t458 tb458 ts458 _ _ ts458_sum ts458_parity
  apply product_cons_b t459 tb459 ts459 _ _ ts459_sum ts459_parity
  apply product_cons_b t460 tb460 ts460 _ _ ts460_sum ts460_parity
  apply product_cons_b t461 tb461 ts461 _ _ ts461_sum ts461_parity
  apply product_cons_b t462 tb462 ts462 _ _ ts462_sum ts462_parity
  apply product_cons_b t463 tb463 ts463 _ _ ts463_sum ts463_parity
  apply product_cons_b t464 tb464 ts464 _ _ ts464_sum ts464_parity
  apply product_cons_b t465 tb465 ts465 _ _ ts465_sum ts465_parity
  apply product_cons_b t466 tb466 ts466 _ _ ts466_sum ts466_parity
  apply product_cons_b t467 tb467 ts467 _ _ ts467_sum ts467_parity
  apply product_cons_b t468 tb468 ts468 _ _ ts468_sum ts468_parity
  apply product_cons_b t469 tb469 ts469 _ _ ts469_sum ts469_parity
  apply product_cons_b t470 tb470 ts470 _ _ ts470_sum ts470_parity
  apply product_cons_b t471 tb471 ts471 _ _ ts471_sum ts471_parity
  apply product_cons_b t472 tb472 ts472 _ _ ts472_sum ts472_parity
  apply product_cons_b t473 tb473 ts473 _ _ ts473_sum ts473_parity
  apply product_cons_b t474 tb474 ts474 _ _ ts474_sum ts474_parity
  apply product_cons_b t475 tb475 ts475 _ _ ts475_sum ts475_parity
  apply product_cons_b t476 tb476 ts476 _ _ ts476_sum ts476_parity
  apply product_cons_b t477 tb477 ts477 _ _ ts477_sum ts477_parity
  apply product_cons_b t478 tb478 ts478 _ _ ts478_sum ts478_parity
  apply product_cons_b t479 tb479 ts479 _ _ ts479_sum ts479_parity
  apply product_cons_b t480 tb480 ts480 _ _ ts480_sum ts480_parity
  apply product_cons_b t481 tb481 ts481 _ _ ts481_sum ts481_parity
  apply product_cons_b t482 tb482 ts482 _ _ ts482_sum ts482_parity
  apply product_cons_b t483 tb483 ts483 _ _ ts483_sum ts483_parity
  apply product_cons_b t484 tb484 ts484 _ _ ts484_sum ts484_parity
  apply product_cons_b t485 tb485 ts485 _ _ ts485_sum ts485_parity
  apply product_cons_b t486 tb486 ts486 _ _ ts486_sum ts486_parity
  apply product_cons_b t487 tb487 ts487 _ _ ts487_sum ts487_parity
  apply product_cons_b t488 tb488 ts488 _ _ ts488_sum ts488_parity
  apply product_cons_b t489 tb489 ts489 _ _ ts489_sum ts489_parity
  apply product_cons_b t490 tb490 ts490 _ _ ts490_sum ts490_parity
  apply product_cons_b t491 tb491 ts491 _ _ ts491_sum ts491_parity
  apply product_cons_b t492 tb492 ts492 _ _ ts492_sum ts492_parity
  apply product_cons_b t493 tb493 ts493 _ _ ts493_sum ts493_parity
  apply product_cons_b t494 tb494 ts494 _ _ ts494_sum ts494_parity
  apply product_cons_b t495 tb495 ts495 _ _ ts495_sum ts495_parity
  apply product_cons_b t496 tb496 ts496 _ _ ts496_sum ts496_parity
  apply product_cons_b t497 tb497 ts497 _ _ ts497_sum ts497_parity
  apply product_cons_b t498 tb498 ts498 _ _ ts498_sum ts498_parity
  apply product_cons_b t499 tb499 ts499 _ _ ts499_sum ts499_parity
  apply product_cons_b t500 tb500 ts500 _ _ ts500_sum ts500_parity
  apply product_cons_b t501 tb501 ts501 _ _ ts501_sum ts501_parity
  apply product_cons_b t502 tb502 ts502 _ _ ts502_sum ts502_parity
  apply product_cons_b t503 tb503 ts503 _ _ ts503_sum ts503_parity
  apply product_cons_b t504 tb504 ts504 _ _ ts504_sum ts504_parity
  apply product_cons_b t505 tb505 ts505 _ _ ts505_sum ts505_parity
  apply product_cons_b t506 tb506 ts506 _ _ ts506_sum ts506_parity
  apply product_cons_b t507 tb507 ts507 _ _ ts507_sum ts507_parity
  apply product_cons_b t508 tb508 ts508 _ _ ts508_sum ts508_parity
  apply product_cons_b t509 tb509 ts509 _ _ ts509_sum ts509_parity
  apply product_cons_b t510 tb510 ts510 _ _ ts510_sum ts510_parity
  apply product_cons_b t511 tb511 ts511 _ _ ts511_sum ts511_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d448 da448 ds448 _ _ ds448_sum ds448_parity
  apply product_cons_a d449 da449 ds449 _ _ ds449_sum ds449_parity
  apply product_cons_a d450 da450 ds450 _ _ ds450_sum ds450_parity
  apply product_cons_a d451 da451 ds451 _ _ ds451_sum ds451_parity
  apply product_cons_a d452 da452 ds452 _ _ ds452_sum ds452_parity
  apply product_cons_a d453 da453 ds453 _ _ ds453_sum ds453_parity
  apply product_cons_a d454 da454 ds454 _ _ ds454_sum ds454_parity
  apply product_cons_a d455 da455 ds455 _ _ ds455_sum ds455_parity
  apply product_cons_a d456 da456 ds456 _ _ ds456_sum ds456_parity
  apply product_cons_a d457 da457 ds457 _ _ ds457_sum ds457_parity
  apply product_cons_a d458 da458 ds458 _ _ ds458_sum ds458_parity
  apply product_cons_a d459 da459 ds459 _ _ ds459_sum ds459_parity
  apply product_cons_a d460 da460 ds460 _ _ ds460_sum ds460_parity
  apply product_cons_a d461 da461 ds461 _ _ ds461_sum ds461_parity
  apply product_cons_a d462 da462 ds462 _ _ ds462_sum ds462_parity
  apply product_cons_a d463 da463 ds463 _ _ ds463_sum ds463_parity
  apply product_cons_a d464 da464 ds464 _ _ ds464_sum ds464_parity
  apply product_cons_a d465 da465 ds465 _ _ ds465_sum ds465_parity
  apply product_cons_a d466 da466 ds466 _ _ ds466_sum ds466_parity
  apply product_cons_a d467 da467 ds467 _ _ ds467_sum ds467_parity
  apply product_cons_a d468 da468 ds468 _ _ ds468_sum ds468_parity
  apply product_cons_a d469 da469 ds469 _ _ ds469_sum ds469_parity
  apply product_cons_a d470 da470 ds470 _ _ ds470_sum ds470_parity
  apply product_cons_a d471 da471 ds471 _ _ ds471_sum ds471_parity
  apply product_cons_a d472 da472 ds472 _ _ ds472_sum ds472_parity
  apply product_cons_a d473 da473 ds473 _ _ ds473_sum ds473_parity
  apply product_cons_a d474 da474 ds474 _ _ ds474_sum ds474_parity
  apply product_cons_a d475 da475 ds475 _ _ ds475_sum ds475_parity
  apply product_cons_a d476 da476 ds476 _ _ ds476_sum ds476_parity
  apply product_cons_a d477 da477 ds477 _ _ ds477_sum ds477_parity
  apply product_cons_a d478 da478 ds478 _ _ ds478_sum ds478_parity
  apply product_cons_a d479 da479 ds479 _ _ ds479_sum ds479_parity
  apply product_cons_a d480 da480 ds480 _ _ ds480_sum ds480_parity
  apply product_cons_a d481 da481 ds481 _ _ ds481_sum ds481_parity
  apply product_cons_a d482 da482 ds482 _ _ ds482_sum ds482_parity
  apply product_cons_a d483 da483 ds483 _ _ ds483_sum ds483_parity
  apply product_cons_a d484 da484 ds484 _ _ ds484_sum ds484_parity
  apply product_cons_a d485 da485 ds485 _ _ ds485_sum ds485_parity
  apply product_cons_a d486 da486 ds486 _ _ ds486_sum ds486_parity
  apply product_cons_a d487 da487 ds487 _ _ ds487_sum ds487_parity
  apply product_cons_a d488 da488 ds488 _ _ ds488_sum ds488_parity
  apply product_cons_a d489 da489 ds489 _ _ ds489_sum ds489_parity
  apply product_cons_a d490 da490 ds490 _ _ ds490_sum ds490_parity
  apply product_cons_a d491 da491 ds491 _ _ ds491_sum ds491_parity
  apply product_cons_a d492 da492 ds492 _ _ ds492_sum ds492_parity
  apply product_cons_a d493 da493 ds493 _ _ ds493_sum ds493_parity
  apply product_cons_a d494 da494 ds494 _ _ ds494_sum ds494_parity
  apply product_cons_a d495 da495 ds495 _ _ ds495_sum ds495_parity
  apply product_cons_a d496 da496 ds496 _ _ ds496_sum ds496_parity
  apply product_cons_a d497 da497 ds497 _ _ ds497_sum ds497_parity
  apply product_cons_a d498 da498 ds498 _ _ ds498_sum ds498_parity
  apply product_cons_a d499 da499 ds499 _ _ ds499_sum ds499_parity
  apply product_cons_a d500 da500 ds500 _ _ ds500_sum ds500_parity
  apply product_cons_a d501 da501 ds501 _ _ ds501_sum ds501_parity
  apply product_cons_a d502 da502 ds502 _ _ ds502_sum ds502_parity
  apply product_cons_a d503 da503 ds503 _ _ ds503_sum ds503_parity
  apply product_cons_a d504 da504 ds504 _ _ ds504_sum ds504_parity
  apply product_cons_a d505 da505 ds505 _ _ ds505_sum ds505_parity
  apply product_cons_a d506 da506 ds506 _ _ ds506_sum ds506_parity
  apply product_cons_a d507 da507 ds507 _ _ ds507_sum ds507_parity
  apply product_cons_a d508 da508 ds508 _ _ ds508_sum ds508_parity
  apply product_cons_a d509 da509 ds509 _ _ ds509_sum ds509_parity
  apply product_cons_a d510 da510 ds510 _ _ ds510_sum ds510_parity
  apply product_cons_a d511 da511 ds511 _ _ ds511_sum ds511_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 448).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 448).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 448).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 448).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 448).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 448).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 448).take 64) RightCertificate.wideSecond ((tbRows.drop 448).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 448).take 64) RightCertificate.wideFirst ((daRows.drop 448).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block07
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
