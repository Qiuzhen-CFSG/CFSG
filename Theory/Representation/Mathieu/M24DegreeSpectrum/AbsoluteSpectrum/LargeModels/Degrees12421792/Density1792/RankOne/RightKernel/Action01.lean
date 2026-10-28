module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.RightKernel.SecondCodes
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.KernelData

/-!
# Checked action 1 of the right-kernel circuit

The original second generator acts on the published input column on
the left. Certified monomial rows use a coordinate read, while dense rows use
the published parity fold. Bounded checks are composed by a list theorem.
See `source/README.md` for the circuit, provenance and measurements.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RightKernelCertificate
open RankOneCertificate

set_option maxRecDepth 8192 in
private theorem block0 :
    actionRange (x0) x1 Data1792.secondRows.toList 0 1280 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 0 1280
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1280 :
    actionRange (x0) x1 Data1792.secondRows.toList 1280 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1280 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1296 :
    actionRange (x0) x1 Data1792.secondRows.toList 1296 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1296 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1312 :
    actionRange (x0) x1 Data1792.secondRows.toList 1312 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1312 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1328 :
    actionRange (x0) x1 Data1792.secondRows.toList 1328 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1328 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1344 :
    actionRange (x0) x1 Data1792.secondRows.toList 1344 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1344 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1360 :
    actionRange (x0) x1 Data1792.secondRows.toList 1360 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1360 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1376 :
    actionRange (x0) x1 Data1792.secondRows.toList 1376 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1376 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1392 :
    actionRange (x0) x1 Data1792.secondRows.toList 1392 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1392 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1408 :
    actionRange (x0) x1 Data1792.secondRows.toList 1408 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1408 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1424 :
    actionRange (x0) x1 Data1792.secondRows.toList 1424 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1424 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1440 :
    actionRange (x0) x1 Data1792.secondRows.toList 1440 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1440 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1456 :
    actionRange (x0) x1 Data1792.secondRows.toList 1456 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1456 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1472 :
    actionRange (x0) x1 Data1792.secondRows.toList 1472 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1472 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1488 :
    actionRange (x0) x1 Data1792.secondRows.toList 1488 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1488 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1504 :
    actionRange (x0) x1 Data1792.secondRows.toList 1504 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1504 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1520 :
    actionRange (x0) x1 Data1792.secondRows.toList 1520 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1520 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1536 :
    actionRange (x0) x1 Data1792.secondRows.toList 1536 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1536 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1552 :
    actionRange (x0) x1 Data1792.secondRows.toList 1552 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1552 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1568 :
    actionRange (x0) x1 Data1792.secondRows.toList 1568 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1568 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1584 :
    actionRange (x0) x1 Data1792.secondRows.toList 1584 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1584 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1600 :
    actionRange (x0) x1 Data1792.secondRows.toList 1600 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1600 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1616 :
    actionRange (x0) x1 Data1792.secondRows.toList 1616 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1616 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1632 :
    actionRange (x0) x1 Data1792.secondRows.toList 1632 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1632 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1648 :
    actionRange (x0) x1 Data1792.secondRows.toList 1648 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1648 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1664 :
    actionRange (x0) x1 Data1792.secondRows.toList 1664 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1664 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1680 :
    actionRange (x0) x1 Data1792.secondRows.toList 1680 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1680 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1696 :
    actionRange (x0) x1 Data1792.secondRows.toList 1696 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1696 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1712 :
    actionRange (x0) x1 Data1792.secondRows.toList 1712 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1712 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1728 :
    actionRange (x0) x1 Data1792.secondRows.toList 1728 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1728 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1744 :
    actionRange (x0) x1 Data1792.secondRows.toList 1744 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1744 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1760 :
    actionRange (x0) x1 Data1792.secondRows.toList 1760 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1760 16
    secondCodes_checked
  decide +kernel

set_option maxRecDepth 8192 in
private theorem block1776 :
    actionRange (x0) x1 Data1792.secondRows.toList 1776 16 = true := by
  apply actionRange_of_check (x0) x1 Data1792.secondRows.toList secondCodes 1776 16
    secondCodes_checked
  decide +kernel

/-- Literal generator action 1; no extra mathematical premises. -/
theorem action01_checked :
    checkAction (x0) x1 Data1792.secondRows.toList = true := by
  apply checkAction_of_range (x0) x1 Data1792.secondRows.toList 1792 (by decide +kernel)
  have join1296 : actionRange (x0) x1 Data1792.secondRows.toList 0 1296 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1280 16 (by decide +kernel)
      block0 block1280
  have join1312 : actionRange (x0) x1 Data1792.secondRows.toList 0 1312 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1296 16 (by decide +kernel)
      join1296 block1296
  have join1328 : actionRange (x0) x1 Data1792.secondRows.toList 0 1328 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1312 16 (by decide +kernel)
      join1312 block1312
  have join1344 : actionRange (x0) x1 Data1792.secondRows.toList 0 1344 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1328 16 (by decide +kernel)
      join1328 block1328
  have join1360 : actionRange (x0) x1 Data1792.secondRows.toList 0 1360 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1344 16 (by decide +kernel)
      join1344 block1344
  have join1376 : actionRange (x0) x1 Data1792.secondRows.toList 0 1376 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1360 16 (by decide +kernel)
      join1360 block1360
  have join1392 : actionRange (x0) x1 Data1792.secondRows.toList 0 1392 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1376 16 (by decide +kernel)
      join1376 block1376
  have join1408 : actionRange (x0) x1 Data1792.secondRows.toList 0 1408 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1392 16 (by decide +kernel)
      join1392 block1392
  have join1424 : actionRange (x0) x1 Data1792.secondRows.toList 0 1424 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1408 16 (by decide +kernel)
      join1408 block1408
  have join1440 : actionRange (x0) x1 Data1792.secondRows.toList 0 1440 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1424 16 (by decide +kernel)
      join1424 block1424
  have join1456 : actionRange (x0) x1 Data1792.secondRows.toList 0 1456 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1440 16 (by decide +kernel)
      join1440 block1440
  have join1472 : actionRange (x0) x1 Data1792.secondRows.toList 0 1472 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1456 16 (by decide +kernel)
      join1456 block1456
  have join1488 : actionRange (x0) x1 Data1792.secondRows.toList 0 1488 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1472 16 (by decide +kernel)
      join1472 block1472
  have join1504 : actionRange (x0) x1 Data1792.secondRows.toList 0 1504 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1488 16 (by decide +kernel)
      join1488 block1488
  have join1520 : actionRange (x0) x1 Data1792.secondRows.toList 0 1520 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1504 16 (by decide +kernel)
      join1504 block1504
  have join1536 : actionRange (x0) x1 Data1792.secondRows.toList 0 1536 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1520 16 (by decide +kernel)
      join1520 block1520
  have join1552 : actionRange (x0) x1 Data1792.secondRows.toList 0 1552 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1536 16 (by decide +kernel)
      join1536 block1536
  have join1568 : actionRange (x0) x1 Data1792.secondRows.toList 0 1568 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1552 16 (by decide +kernel)
      join1552 block1552
  have join1584 : actionRange (x0) x1 Data1792.secondRows.toList 0 1584 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1568 16 (by decide +kernel)
      join1568 block1568
  have join1600 : actionRange (x0) x1 Data1792.secondRows.toList 0 1600 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1584 16 (by decide +kernel)
      join1584 block1584
  have join1616 : actionRange (x0) x1 Data1792.secondRows.toList 0 1616 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1600 16 (by decide +kernel)
      join1600 block1600
  have join1632 : actionRange (x0) x1 Data1792.secondRows.toList 0 1632 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1616 16 (by decide +kernel)
      join1616 block1616
  have join1648 : actionRange (x0) x1 Data1792.secondRows.toList 0 1648 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1632 16 (by decide +kernel)
      join1632 block1632
  have join1664 : actionRange (x0) x1 Data1792.secondRows.toList 0 1664 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1648 16 (by decide +kernel)
      join1648 block1648
  have join1680 : actionRange (x0) x1 Data1792.secondRows.toList 0 1680 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1664 16 (by decide +kernel)
      join1664 block1664
  have join1696 : actionRange (x0) x1 Data1792.secondRows.toList 0 1696 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1680 16 (by decide +kernel)
      join1680 block1680
  have join1712 : actionRange (x0) x1 Data1792.secondRows.toList 0 1712 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1696 16 (by decide +kernel)
      join1696 block1696
  have join1728 : actionRange (x0) x1 Data1792.secondRows.toList 0 1728 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1712 16 (by decide +kernel)
      join1712 block1712
  have join1744 : actionRange (x0) x1 Data1792.secondRows.toList 0 1744 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1728 16 (by decide +kernel)
      join1728 block1728
  have join1760 : actionRange (x0) x1 Data1792.secondRows.toList 0 1760 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1744 16 (by decide +kernel)
      join1744 block1744
  have join1776 : actionRange (x0) x1 Data1792.secondRows.toList 0 1776 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1760 16 (by decide +kernel)
      join1760 block1760
  have join1792 : actionRange (x0) x1 Data1792.secondRows.toList 0 1792 = true :=
    actionRange_join (x0) x1 Data1792.secondRows.toList 0 1776 16 (by decide +kernel)
      join1776 block1776
  exact join1792

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RightKernelCertificate
