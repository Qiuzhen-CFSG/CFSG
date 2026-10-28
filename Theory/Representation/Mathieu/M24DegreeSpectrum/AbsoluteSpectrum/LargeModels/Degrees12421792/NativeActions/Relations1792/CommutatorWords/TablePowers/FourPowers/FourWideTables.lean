module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.FourPowers.FourWideData

/-!
# Checked radix expansion of the four table

Individual row checks assemble every block; list-map congruence joins the blocks.
All checks use kernel reduction; numeric generation supplies no proof evidence.
Source: ATLAS M24G1-P1; see `../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.FourPowers
open Arithmetic GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data

set_option Elab.async false

set_option maxRecDepth 8192 in
private theorem expanded00_row00 : fourWide00[0]! =
    expandTree 6 1792 fourRows00[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row01 : fourWide00[1]! =
    expandTree 6 1792 fourRows00[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row02 : fourWide00[2]! =
    expandTree 6 1792 fourRows00[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row03 : fourWide00[3]! =
    expandTree 6 1792 fourRows00[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row04 : fourWide00[4]! =
    expandTree 6 1792 fourRows00[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row05 : fourWide00[5]! =
    expandTree 6 1792 fourRows00[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row06 : fourWide00[6]! =
    expandTree 6 1792 fourRows00[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row07 : fourWide00[7]! =
    expandTree 6 1792 fourRows00[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row08 : fourWide00[8]! =
    expandTree 6 1792 fourRows00[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row09 : fourWide00[9]! =
    expandTree 6 1792 fourRows00[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row10 : fourWide00[10]! =
    expandTree 6 1792 fourRows00[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row11 : fourWide00[11]! =
    expandTree 6 1792 fourRows00[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row12 : fourWide00[12]! =
    expandTree 6 1792 fourRows00[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row13 : fourWide00[13]! =
    expandTree 6 1792 fourRows00[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row14 : fourWide00[14]! =
    expandTree 6 1792 fourRows00[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row15 : fourWide00[15]! =
    expandTree 6 1792 fourRows00[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row16 : fourWide00[16]! =
    expandTree 6 1792 fourRows00[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row17 : fourWide00[17]! =
    expandTree 6 1792 fourRows00[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row18 : fourWide00[18]! =
    expandTree 6 1792 fourRows00[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row19 : fourWide00[19]! =
    expandTree 6 1792 fourRows00[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row20 : fourWide00[20]! =
    expandTree 6 1792 fourRows00[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row21 : fourWide00[21]! =
    expandTree 6 1792 fourRows00[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row22 : fourWide00[22]! =
    expandTree 6 1792 fourRows00[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row23 : fourWide00[23]! =
    expandTree 6 1792 fourRows00[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row24 : fourWide00[24]! =
    expandTree 6 1792 fourRows00[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row25 : fourWide00[25]! =
    expandTree 6 1792 fourRows00[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row26 : fourWide00[26]! =
    expandTree 6 1792 fourRows00[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row27 : fourWide00[27]! =
    expandTree 6 1792 fourRows00[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row28 : fourWide00[28]! =
    expandTree 6 1792 fourRows00[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row29 : fourWide00[29]! =
    expandTree 6 1792 fourRows00[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row30 : fourWide00[30]! =
    expandTree 6 1792 fourRows00[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded00_row31 : fourWide00[31]! =
    expandTree 6 1792 fourRows00[31]! := by decide +kernel

private theorem expanded00 : fourWide00 =
    fourRows00.map (expandTree 6 1792) := by
  change [fourWide00[0]!,
    fourWide00[1]!,
    fourWide00[2]!,
    fourWide00[3]!,
    fourWide00[4]!,
    fourWide00[5]!,
    fourWide00[6]!,
    fourWide00[7]!,
    fourWide00[8]!,
    fourWide00[9]!,
    fourWide00[10]!,
    fourWide00[11]!,
    fourWide00[12]!,
    fourWide00[13]!,
    fourWide00[14]!,
    fourWide00[15]!,
    fourWide00[16]!,
    fourWide00[17]!,
    fourWide00[18]!,
    fourWide00[19]!,
    fourWide00[20]!,
    fourWide00[21]!,
    fourWide00[22]!,
    fourWide00[23]!,
    fourWide00[24]!,
    fourWide00[25]!,
    fourWide00[26]!,
    fourWide00[27]!,
    fourWide00[28]!,
    fourWide00[29]!,
    fourWide00[30]!,
    fourWide00[31]!] =
    [expandTree 6 1792 fourRows00[0]!,
     expandTree 6 1792 fourRows00[1]!,
     expandTree 6 1792 fourRows00[2]!,
     expandTree 6 1792 fourRows00[3]!,
     expandTree 6 1792 fourRows00[4]!,
     expandTree 6 1792 fourRows00[5]!,
     expandTree 6 1792 fourRows00[6]!,
     expandTree 6 1792 fourRows00[7]!,
     expandTree 6 1792 fourRows00[8]!,
     expandTree 6 1792 fourRows00[9]!,
     expandTree 6 1792 fourRows00[10]!,
     expandTree 6 1792 fourRows00[11]!,
     expandTree 6 1792 fourRows00[12]!,
     expandTree 6 1792 fourRows00[13]!,
     expandTree 6 1792 fourRows00[14]!,
     expandTree 6 1792 fourRows00[15]!,
     expandTree 6 1792 fourRows00[16]!,
     expandTree 6 1792 fourRows00[17]!,
     expandTree 6 1792 fourRows00[18]!,
     expandTree 6 1792 fourRows00[19]!,
     expandTree 6 1792 fourRows00[20]!,
     expandTree 6 1792 fourRows00[21]!,
     expandTree 6 1792 fourRows00[22]!,
     expandTree 6 1792 fourRows00[23]!,
     expandTree 6 1792 fourRows00[24]!,
     expandTree 6 1792 fourRows00[25]!,
     expandTree 6 1792 fourRows00[26]!,
     expandTree 6 1792 fourRows00[27]!,
     expandTree 6 1792 fourRows00[28]!,
     expandTree 6 1792 fourRows00[29]!,
     expandTree 6 1792 fourRows00[30]!,
     expandTree 6 1792 fourRows00[31]!]
  rw [expanded00_row00, expanded00_row01, expanded00_row02, expanded00_row03, expanded00_row04, expanded00_row05, expanded00_row06, expanded00_row07, expanded00_row08, expanded00_row09, expanded00_row10, expanded00_row11, expanded00_row12, expanded00_row13, expanded00_row14, expanded00_row15, expanded00_row16, expanded00_row17, expanded00_row18, expanded00_row19, expanded00_row20, expanded00_row21, expanded00_row22, expanded00_row23, expanded00_row24, expanded00_row25, expanded00_row26, expanded00_row27, expanded00_row28, expanded00_row29, expanded00_row30, expanded00_row31]

set_option maxRecDepth 8192 in
private theorem expanded01_row00 : fourWide01[0]! =
    expandTree 6 1792 fourRows01[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row01 : fourWide01[1]! =
    expandTree 6 1792 fourRows01[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row02 : fourWide01[2]! =
    expandTree 6 1792 fourRows01[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row03 : fourWide01[3]! =
    expandTree 6 1792 fourRows01[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row04 : fourWide01[4]! =
    expandTree 6 1792 fourRows01[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row05 : fourWide01[5]! =
    expandTree 6 1792 fourRows01[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row06 : fourWide01[6]! =
    expandTree 6 1792 fourRows01[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row07 : fourWide01[7]! =
    expandTree 6 1792 fourRows01[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row08 : fourWide01[8]! =
    expandTree 6 1792 fourRows01[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row09 : fourWide01[9]! =
    expandTree 6 1792 fourRows01[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row10 : fourWide01[10]! =
    expandTree 6 1792 fourRows01[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row11 : fourWide01[11]! =
    expandTree 6 1792 fourRows01[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row12 : fourWide01[12]! =
    expandTree 6 1792 fourRows01[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row13 : fourWide01[13]! =
    expandTree 6 1792 fourRows01[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row14 : fourWide01[14]! =
    expandTree 6 1792 fourRows01[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row15 : fourWide01[15]! =
    expandTree 6 1792 fourRows01[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row16 : fourWide01[16]! =
    expandTree 6 1792 fourRows01[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row17 : fourWide01[17]! =
    expandTree 6 1792 fourRows01[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row18 : fourWide01[18]! =
    expandTree 6 1792 fourRows01[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row19 : fourWide01[19]! =
    expandTree 6 1792 fourRows01[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row20 : fourWide01[20]! =
    expandTree 6 1792 fourRows01[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row21 : fourWide01[21]! =
    expandTree 6 1792 fourRows01[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row22 : fourWide01[22]! =
    expandTree 6 1792 fourRows01[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row23 : fourWide01[23]! =
    expandTree 6 1792 fourRows01[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row24 : fourWide01[24]! =
    expandTree 6 1792 fourRows01[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row25 : fourWide01[25]! =
    expandTree 6 1792 fourRows01[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row26 : fourWide01[26]! =
    expandTree 6 1792 fourRows01[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row27 : fourWide01[27]! =
    expandTree 6 1792 fourRows01[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row28 : fourWide01[28]! =
    expandTree 6 1792 fourRows01[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row29 : fourWide01[29]! =
    expandTree 6 1792 fourRows01[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row30 : fourWide01[30]! =
    expandTree 6 1792 fourRows01[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded01_row31 : fourWide01[31]! =
    expandTree 6 1792 fourRows01[31]! := by decide +kernel

private theorem expanded01 : fourWide01 =
    fourRows01.map (expandTree 6 1792) := by
  change [fourWide01[0]!,
    fourWide01[1]!,
    fourWide01[2]!,
    fourWide01[3]!,
    fourWide01[4]!,
    fourWide01[5]!,
    fourWide01[6]!,
    fourWide01[7]!,
    fourWide01[8]!,
    fourWide01[9]!,
    fourWide01[10]!,
    fourWide01[11]!,
    fourWide01[12]!,
    fourWide01[13]!,
    fourWide01[14]!,
    fourWide01[15]!,
    fourWide01[16]!,
    fourWide01[17]!,
    fourWide01[18]!,
    fourWide01[19]!,
    fourWide01[20]!,
    fourWide01[21]!,
    fourWide01[22]!,
    fourWide01[23]!,
    fourWide01[24]!,
    fourWide01[25]!,
    fourWide01[26]!,
    fourWide01[27]!,
    fourWide01[28]!,
    fourWide01[29]!,
    fourWide01[30]!,
    fourWide01[31]!] =
    [expandTree 6 1792 fourRows01[0]!,
     expandTree 6 1792 fourRows01[1]!,
     expandTree 6 1792 fourRows01[2]!,
     expandTree 6 1792 fourRows01[3]!,
     expandTree 6 1792 fourRows01[4]!,
     expandTree 6 1792 fourRows01[5]!,
     expandTree 6 1792 fourRows01[6]!,
     expandTree 6 1792 fourRows01[7]!,
     expandTree 6 1792 fourRows01[8]!,
     expandTree 6 1792 fourRows01[9]!,
     expandTree 6 1792 fourRows01[10]!,
     expandTree 6 1792 fourRows01[11]!,
     expandTree 6 1792 fourRows01[12]!,
     expandTree 6 1792 fourRows01[13]!,
     expandTree 6 1792 fourRows01[14]!,
     expandTree 6 1792 fourRows01[15]!,
     expandTree 6 1792 fourRows01[16]!,
     expandTree 6 1792 fourRows01[17]!,
     expandTree 6 1792 fourRows01[18]!,
     expandTree 6 1792 fourRows01[19]!,
     expandTree 6 1792 fourRows01[20]!,
     expandTree 6 1792 fourRows01[21]!,
     expandTree 6 1792 fourRows01[22]!,
     expandTree 6 1792 fourRows01[23]!,
     expandTree 6 1792 fourRows01[24]!,
     expandTree 6 1792 fourRows01[25]!,
     expandTree 6 1792 fourRows01[26]!,
     expandTree 6 1792 fourRows01[27]!,
     expandTree 6 1792 fourRows01[28]!,
     expandTree 6 1792 fourRows01[29]!,
     expandTree 6 1792 fourRows01[30]!,
     expandTree 6 1792 fourRows01[31]!]
  rw [expanded01_row00, expanded01_row01, expanded01_row02, expanded01_row03, expanded01_row04, expanded01_row05, expanded01_row06, expanded01_row07, expanded01_row08, expanded01_row09, expanded01_row10, expanded01_row11, expanded01_row12, expanded01_row13, expanded01_row14, expanded01_row15, expanded01_row16, expanded01_row17, expanded01_row18, expanded01_row19, expanded01_row20, expanded01_row21, expanded01_row22, expanded01_row23, expanded01_row24, expanded01_row25, expanded01_row26, expanded01_row27, expanded01_row28, expanded01_row29, expanded01_row30, expanded01_row31]

set_option maxRecDepth 8192 in
private theorem expanded02_row00 : fourWide02[0]! =
    expandTree 6 1792 fourRows02[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row01 : fourWide02[1]! =
    expandTree 6 1792 fourRows02[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row02 : fourWide02[2]! =
    expandTree 6 1792 fourRows02[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row03 : fourWide02[3]! =
    expandTree 6 1792 fourRows02[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row04 : fourWide02[4]! =
    expandTree 6 1792 fourRows02[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row05 : fourWide02[5]! =
    expandTree 6 1792 fourRows02[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row06 : fourWide02[6]! =
    expandTree 6 1792 fourRows02[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row07 : fourWide02[7]! =
    expandTree 6 1792 fourRows02[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row08 : fourWide02[8]! =
    expandTree 6 1792 fourRows02[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row09 : fourWide02[9]! =
    expandTree 6 1792 fourRows02[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row10 : fourWide02[10]! =
    expandTree 6 1792 fourRows02[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row11 : fourWide02[11]! =
    expandTree 6 1792 fourRows02[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row12 : fourWide02[12]! =
    expandTree 6 1792 fourRows02[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row13 : fourWide02[13]! =
    expandTree 6 1792 fourRows02[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row14 : fourWide02[14]! =
    expandTree 6 1792 fourRows02[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row15 : fourWide02[15]! =
    expandTree 6 1792 fourRows02[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row16 : fourWide02[16]! =
    expandTree 6 1792 fourRows02[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row17 : fourWide02[17]! =
    expandTree 6 1792 fourRows02[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row18 : fourWide02[18]! =
    expandTree 6 1792 fourRows02[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row19 : fourWide02[19]! =
    expandTree 6 1792 fourRows02[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row20 : fourWide02[20]! =
    expandTree 6 1792 fourRows02[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row21 : fourWide02[21]! =
    expandTree 6 1792 fourRows02[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row22 : fourWide02[22]! =
    expandTree 6 1792 fourRows02[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row23 : fourWide02[23]! =
    expandTree 6 1792 fourRows02[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row24 : fourWide02[24]! =
    expandTree 6 1792 fourRows02[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row25 : fourWide02[25]! =
    expandTree 6 1792 fourRows02[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row26 : fourWide02[26]! =
    expandTree 6 1792 fourRows02[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row27 : fourWide02[27]! =
    expandTree 6 1792 fourRows02[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row28 : fourWide02[28]! =
    expandTree 6 1792 fourRows02[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row29 : fourWide02[29]! =
    expandTree 6 1792 fourRows02[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row30 : fourWide02[30]! =
    expandTree 6 1792 fourRows02[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded02_row31 : fourWide02[31]! =
    expandTree 6 1792 fourRows02[31]! := by decide +kernel

private theorem expanded02 : fourWide02 =
    fourRows02.map (expandTree 6 1792) := by
  change [fourWide02[0]!,
    fourWide02[1]!,
    fourWide02[2]!,
    fourWide02[3]!,
    fourWide02[4]!,
    fourWide02[5]!,
    fourWide02[6]!,
    fourWide02[7]!,
    fourWide02[8]!,
    fourWide02[9]!,
    fourWide02[10]!,
    fourWide02[11]!,
    fourWide02[12]!,
    fourWide02[13]!,
    fourWide02[14]!,
    fourWide02[15]!,
    fourWide02[16]!,
    fourWide02[17]!,
    fourWide02[18]!,
    fourWide02[19]!,
    fourWide02[20]!,
    fourWide02[21]!,
    fourWide02[22]!,
    fourWide02[23]!,
    fourWide02[24]!,
    fourWide02[25]!,
    fourWide02[26]!,
    fourWide02[27]!,
    fourWide02[28]!,
    fourWide02[29]!,
    fourWide02[30]!,
    fourWide02[31]!] =
    [expandTree 6 1792 fourRows02[0]!,
     expandTree 6 1792 fourRows02[1]!,
     expandTree 6 1792 fourRows02[2]!,
     expandTree 6 1792 fourRows02[3]!,
     expandTree 6 1792 fourRows02[4]!,
     expandTree 6 1792 fourRows02[5]!,
     expandTree 6 1792 fourRows02[6]!,
     expandTree 6 1792 fourRows02[7]!,
     expandTree 6 1792 fourRows02[8]!,
     expandTree 6 1792 fourRows02[9]!,
     expandTree 6 1792 fourRows02[10]!,
     expandTree 6 1792 fourRows02[11]!,
     expandTree 6 1792 fourRows02[12]!,
     expandTree 6 1792 fourRows02[13]!,
     expandTree 6 1792 fourRows02[14]!,
     expandTree 6 1792 fourRows02[15]!,
     expandTree 6 1792 fourRows02[16]!,
     expandTree 6 1792 fourRows02[17]!,
     expandTree 6 1792 fourRows02[18]!,
     expandTree 6 1792 fourRows02[19]!,
     expandTree 6 1792 fourRows02[20]!,
     expandTree 6 1792 fourRows02[21]!,
     expandTree 6 1792 fourRows02[22]!,
     expandTree 6 1792 fourRows02[23]!,
     expandTree 6 1792 fourRows02[24]!,
     expandTree 6 1792 fourRows02[25]!,
     expandTree 6 1792 fourRows02[26]!,
     expandTree 6 1792 fourRows02[27]!,
     expandTree 6 1792 fourRows02[28]!,
     expandTree 6 1792 fourRows02[29]!,
     expandTree 6 1792 fourRows02[30]!,
     expandTree 6 1792 fourRows02[31]!]
  rw [expanded02_row00, expanded02_row01, expanded02_row02, expanded02_row03, expanded02_row04, expanded02_row05, expanded02_row06, expanded02_row07, expanded02_row08, expanded02_row09, expanded02_row10, expanded02_row11, expanded02_row12, expanded02_row13, expanded02_row14, expanded02_row15, expanded02_row16, expanded02_row17, expanded02_row18, expanded02_row19, expanded02_row20, expanded02_row21, expanded02_row22, expanded02_row23, expanded02_row24, expanded02_row25, expanded02_row26, expanded02_row27, expanded02_row28, expanded02_row29, expanded02_row30, expanded02_row31]

set_option maxRecDepth 8192 in
private theorem expanded03_row00 : fourWide03[0]! =
    expandTree 6 1792 fourRows03[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row01 : fourWide03[1]! =
    expandTree 6 1792 fourRows03[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row02 : fourWide03[2]! =
    expandTree 6 1792 fourRows03[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row03 : fourWide03[3]! =
    expandTree 6 1792 fourRows03[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row04 : fourWide03[4]! =
    expandTree 6 1792 fourRows03[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row05 : fourWide03[5]! =
    expandTree 6 1792 fourRows03[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row06 : fourWide03[6]! =
    expandTree 6 1792 fourRows03[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row07 : fourWide03[7]! =
    expandTree 6 1792 fourRows03[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row08 : fourWide03[8]! =
    expandTree 6 1792 fourRows03[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row09 : fourWide03[9]! =
    expandTree 6 1792 fourRows03[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row10 : fourWide03[10]! =
    expandTree 6 1792 fourRows03[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row11 : fourWide03[11]! =
    expandTree 6 1792 fourRows03[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row12 : fourWide03[12]! =
    expandTree 6 1792 fourRows03[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row13 : fourWide03[13]! =
    expandTree 6 1792 fourRows03[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row14 : fourWide03[14]! =
    expandTree 6 1792 fourRows03[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row15 : fourWide03[15]! =
    expandTree 6 1792 fourRows03[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row16 : fourWide03[16]! =
    expandTree 6 1792 fourRows03[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row17 : fourWide03[17]! =
    expandTree 6 1792 fourRows03[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row18 : fourWide03[18]! =
    expandTree 6 1792 fourRows03[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row19 : fourWide03[19]! =
    expandTree 6 1792 fourRows03[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row20 : fourWide03[20]! =
    expandTree 6 1792 fourRows03[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row21 : fourWide03[21]! =
    expandTree 6 1792 fourRows03[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row22 : fourWide03[22]! =
    expandTree 6 1792 fourRows03[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row23 : fourWide03[23]! =
    expandTree 6 1792 fourRows03[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row24 : fourWide03[24]! =
    expandTree 6 1792 fourRows03[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row25 : fourWide03[25]! =
    expandTree 6 1792 fourRows03[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row26 : fourWide03[26]! =
    expandTree 6 1792 fourRows03[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row27 : fourWide03[27]! =
    expandTree 6 1792 fourRows03[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row28 : fourWide03[28]! =
    expandTree 6 1792 fourRows03[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row29 : fourWide03[29]! =
    expandTree 6 1792 fourRows03[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row30 : fourWide03[30]! =
    expandTree 6 1792 fourRows03[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded03_row31 : fourWide03[31]! =
    expandTree 6 1792 fourRows03[31]! := by decide +kernel

private theorem expanded03 : fourWide03 =
    fourRows03.map (expandTree 6 1792) := by
  change [fourWide03[0]!,
    fourWide03[1]!,
    fourWide03[2]!,
    fourWide03[3]!,
    fourWide03[4]!,
    fourWide03[5]!,
    fourWide03[6]!,
    fourWide03[7]!,
    fourWide03[8]!,
    fourWide03[9]!,
    fourWide03[10]!,
    fourWide03[11]!,
    fourWide03[12]!,
    fourWide03[13]!,
    fourWide03[14]!,
    fourWide03[15]!,
    fourWide03[16]!,
    fourWide03[17]!,
    fourWide03[18]!,
    fourWide03[19]!,
    fourWide03[20]!,
    fourWide03[21]!,
    fourWide03[22]!,
    fourWide03[23]!,
    fourWide03[24]!,
    fourWide03[25]!,
    fourWide03[26]!,
    fourWide03[27]!,
    fourWide03[28]!,
    fourWide03[29]!,
    fourWide03[30]!,
    fourWide03[31]!] =
    [expandTree 6 1792 fourRows03[0]!,
     expandTree 6 1792 fourRows03[1]!,
     expandTree 6 1792 fourRows03[2]!,
     expandTree 6 1792 fourRows03[3]!,
     expandTree 6 1792 fourRows03[4]!,
     expandTree 6 1792 fourRows03[5]!,
     expandTree 6 1792 fourRows03[6]!,
     expandTree 6 1792 fourRows03[7]!,
     expandTree 6 1792 fourRows03[8]!,
     expandTree 6 1792 fourRows03[9]!,
     expandTree 6 1792 fourRows03[10]!,
     expandTree 6 1792 fourRows03[11]!,
     expandTree 6 1792 fourRows03[12]!,
     expandTree 6 1792 fourRows03[13]!,
     expandTree 6 1792 fourRows03[14]!,
     expandTree 6 1792 fourRows03[15]!,
     expandTree 6 1792 fourRows03[16]!,
     expandTree 6 1792 fourRows03[17]!,
     expandTree 6 1792 fourRows03[18]!,
     expandTree 6 1792 fourRows03[19]!,
     expandTree 6 1792 fourRows03[20]!,
     expandTree 6 1792 fourRows03[21]!,
     expandTree 6 1792 fourRows03[22]!,
     expandTree 6 1792 fourRows03[23]!,
     expandTree 6 1792 fourRows03[24]!,
     expandTree 6 1792 fourRows03[25]!,
     expandTree 6 1792 fourRows03[26]!,
     expandTree 6 1792 fourRows03[27]!,
     expandTree 6 1792 fourRows03[28]!,
     expandTree 6 1792 fourRows03[29]!,
     expandTree 6 1792 fourRows03[30]!,
     expandTree 6 1792 fourRows03[31]!]
  rw [expanded03_row00, expanded03_row01, expanded03_row02, expanded03_row03, expanded03_row04, expanded03_row05, expanded03_row06, expanded03_row07, expanded03_row08, expanded03_row09, expanded03_row10, expanded03_row11, expanded03_row12, expanded03_row13, expanded03_row14, expanded03_row15, expanded03_row16, expanded03_row17, expanded03_row18, expanded03_row19, expanded03_row20, expanded03_row21, expanded03_row22, expanded03_row23, expanded03_row24, expanded03_row25, expanded03_row26, expanded03_row27, expanded03_row28, expanded03_row29, expanded03_row30, expanded03_row31]

set_option maxRecDepth 8192 in
private theorem expanded04_row00 : fourWide04[0]! =
    expandTree 6 1792 fourRows04[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row01 : fourWide04[1]! =
    expandTree 6 1792 fourRows04[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row02 : fourWide04[2]! =
    expandTree 6 1792 fourRows04[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row03 : fourWide04[3]! =
    expandTree 6 1792 fourRows04[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row04 : fourWide04[4]! =
    expandTree 6 1792 fourRows04[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row05 : fourWide04[5]! =
    expandTree 6 1792 fourRows04[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row06 : fourWide04[6]! =
    expandTree 6 1792 fourRows04[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row07 : fourWide04[7]! =
    expandTree 6 1792 fourRows04[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row08 : fourWide04[8]! =
    expandTree 6 1792 fourRows04[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row09 : fourWide04[9]! =
    expandTree 6 1792 fourRows04[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row10 : fourWide04[10]! =
    expandTree 6 1792 fourRows04[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row11 : fourWide04[11]! =
    expandTree 6 1792 fourRows04[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row12 : fourWide04[12]! =
    expandTree 6 1792 fourRows04[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row13 : fourWide04[13]! =
    expandTree 6 1792 fourRows04[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row14 : fourWide04[14]! =
    expandTree 6 1792 fourRows04[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row15 : fourWide04[15]! =
    expandTree 6 1792 fourRows04[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row16 : fourWide04[16]! =
    expandTree 6 1792 fourRows04[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row17 : fourWide04[17]! =
    expandTree 6 1792 fourRows04[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row18 : fourWide04[18]! =
    expandTree 6 1792 fourRows04[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row19 : fourWide04[19]! =
    expandTree 6 1792 fourRows04[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row20 : fourWide04[20]! =
    expandTree 6 1792 fourRows04[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row21 : fourWide04[21]! =
    expandTree 6 1792 fourRows04[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row22 : fourWide04[22]! =
    expandTree 6 1792 fourRows04[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row23 : fourWide04[23]! =
    expandTree 6 1792 fourRows04[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row24 : fourWide04[24]! =
    expandTree 6 1792 fourRows04[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row25 : fourWide04[25]! =
    expandTree 6 1792 fourRows04[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row26 : fourWide04[26]! =
    expandTree 6 1792 fourRows04[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row27 : fourWide04[27]! =
    expandTree 6 1792 fourRows04[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row28 : fourWide04[28]! =
    expandTree 6 1792 fourRows04[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row29 : fourWide04[29]! =
    expandTree 6 1792 fourRows04[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row30 : fourWide04[30]! =
    expandTree 6 1792 fourRows04[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded04_row31 : fourWide04[31]! =
    expandTree 6 1792 fourRows04[31]! := by decide +kernel

private theorem expanded04 : fourWide04 =
    fourRows04.map (expandTree 6 1792) := by
  change [fourWide04[0]!,
    fourWide04[1]!,
    fourWide04[2]!,
    fourWide04[3]!,
    fourWide04[4]!,
    fourWide04[5]!,
    fourWide04[6]!,
    fourWide04[7]!,
    fourWide04[8]!,
    fourWide04[9]!,
    fourWide04[10]!,
    fourWide04[11]!,
    fourWide04[12]!,
    fourWide04[13]!,
    fourWide04[14]!,
    fourWide04[15]!,
    fourWide04[16]!,
    fourWide04[17]!,
    fourWide04[18]!,
    fourWide04[19]!,
    fourWide04[20]!,
    fourWide04[21]!,
    fourWide04[22]!,
    fourWide04[23]!,
    fourWide04[24]!,
    fourWide04[25]!,
    fourWide04[26]!,
    fourWide04[27]!,
    fourWide04[28]!,
    fourWide04[29]!,
    fourWide04[30]!,
    fourWide04[31]!] =
    [expandTree 6 1792 fourRows04[0]!,
     expandTree 6 1792 fourRows04[1]!,
     expandTree 6 1792 fourRows04[2]!,
     expandTree 6 1792 fourRows04[3]!,
     expandTree 6 1792 fourRows04[4]!,
     expandTree 6 1792 fourRows04[5]!,
     expandTree 6 1792 fourRows04[6]!,
     expandTree 6 1792 fourRows04[7]!,
     expandTree 6 1792 fourRows04[8]!,
     expandTree 6 1792 fourRows04[9]!,
     expandTree 6 1792 fourRows04[10]!,
     expandTree 6 1792 fourRows04[11]!,
     expandTree 6 1792 fourRows04[12]!,
     expandTree 6 1792 fourRows04[13]!,
     expandTree 6 1792 fourRows04[14]!,
     expandTree 6 1792 fourRows04[15]!,
     expandTree 6 1792 fourRows04[16]!,
     expandTree 6 1792 fourRows04[17]!,
     expandTree 6 1792 fourRows04[18]!,
     expandTree 6 1792 fourRows04[19]!,
     expandTree 6 1792 fourRows04[20]!,
     expandTree 6 1792 fourRows04[21]!,
     expandTree 6 1792 fourRows04[22]!,
     expandTree 6 1792 fourRows04[23]!,
     expandTree 6 1792 fourRows04[24]!,
     expandTree 6 1792 fourRows04[25]!,
     expandTree 6 1792 fourRows04[26]!,
     expandTree 6 1792 fourRows04[27]!,
     expandTree 6 1792 fourRows04[28]!,
     expandTree 6 1792 fourRows04[29]!,
     expandTree 6 1792 fourRows04[30]!,
     expandTree 6 1792 fourRows04[31]!]
  rw [expanded04_row00, expanded04_row01, expanded04_row02, expanded04_row03, expanded04_row04, expanded04_row05, expanded04_row06, expanded04_row07, expanded04_row08, expanded04_row09, expanded04_row10, expanded04_row11, expanded04_row12, expanded04_row13, expanded04_row14, expanded04_row15, expanded04_row16, expanded04_row17, expanded04_row18, expanded04_row19, expanded04_row20, expanded04_row21, expanded04_row22, expanded04_row23, expanded04_row24, expanded04_row25, expanded04_row26, expanded04_row27, expanded04_row28, expanded04_row29, expanded04_row30, expanded04_row31]

set_option maxRecDepth 8192 in
private theorem expanded05_row00 : fourWide05[0]! =
    expandTree 6 1792 fourRows05[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row01 : fourWide05[1]! =
    expandTree 6 1792 fourRows05[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row02 : fourWide05[2]! =
    expandTree 6 1792 fourRows05[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row03 : fourWide05[3]! =
    expandTree 6 1792 fourRows05[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row04 : fourWide05[4]! =
    expandTree 6 1792 fourRows05[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row05 : fourWide05[5]! =
    expandTree 6 1792 fourRows05[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row06 : fourWide05[6]! =
    expandTree 6 1792 fourRows05[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row07 : fourWide05[7]! =
    expandTree 6 1792 fourRows05[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row08 : fourWide05[8]! =
    expandTree 6 1792 fourRows05[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row09 : fourWide05[9]! =
    expandTree 6 1792 fourRows05[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row10 : fourWide05[10]! =
    expandTree 6 1792 fourRows05[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row11 : fourWide05[11]! =
    expandTree 6 1792 fourRows05[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row12 : fourWide05[12]! =
    expandTree 6 1792 fourRows05[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row13 : fourWide05[13]! =
    expandTree 6 1792 fourRows05[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row14 : fourWide05[14]! =
    expandTree 6 1792 fourRows05[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row15 : fourWide05[15]! =
    expandTree 6 1792 fourRows05[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row16 : fourWide05[16]! =
    expandTree 6 1792 fourRows05[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row17 : fourWide05[17]! =
    expandTree 6 1792 fourRows05[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row18 : fourWide05[18]! =
    expandTree 6 1792 fourRows05[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row19 : fourWide05[19]! =
    expandTree 6 1792 fourRows05[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row20 : fourWide05[20]! =
    expandTree 6 1792 fourRows05[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row21 : fourWide05[21]! =
    expandTree 6 1792 fourRows05[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row22 : fourWide05[22]! =
    expandTree 6 1792 fourRows05[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row23 : fourWide05[23]! =
    expandTree 6 1792 fourRows05[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row24 : fourWide05[24]! =
    expandTree 6 1792 fourRows05[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row25 : fourWide05[25]! =
    expandTree 6 1792 fourRows05[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row26 : fourWide05[26]! =
    expandTree 6 1792 fourRows05[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row27 : fourWide05[27]! =
    expandTree 6 1792 fourRows05[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row28 : fourWide05[28]! =
    expandTree 6 1792 fourRows05[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row29 : fourWide05[29]! =
    expandTree 6 1792 fourRows05[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row30 : fourWide05[30]! =
    expandTree 6 1792 fourRows05[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded05_row31 : fourWide05[31]! =
    expandTree 6 1792 fourRows05[31]! := by decide +kernel

private theorem expanded05 : fourWide05 =
    fourRows05.map (expandTree 6 1792) := by
  change [fourWide05[0]!,
    fourWide05[1]!,
    fourWide05[2]!,
    fourWide05[3]!,
    fourWide05[4]!,
    fourWide05[5]!,
    fourWide05[6]!,
    fourWide05[7]!,
    fourWide05[8]!,
    fourWide05[9]!,
    fourWide05[10]!,
    fourWide05[11]!,
    fourWide05[12]!,
    fourWide05[13]!,
    fourWide05[14]!,
    fourWide05[15]!,
    fourWide05[16]!,
    fourWide05[17]!,
    fourWide05[18]!,
    fourWide05[19]!,
    fourWide05[20]!,
    fourWide05[21]!,
    fourWide05[22]!,
    fourWide05[23]!,
    fourWide05[24]!,
    fourWide05[25]!,
    fourWide05[26]!,
    fourWide05[27]!,
    fourWide05[28]!,
    fourWide05[29]!,
    fourWide05[30]!,
    fourWide05[31]!] =
    [expandTree 6 1792 fourRows05[0]!,
     expandTree 6 1792 fourRows05[1]!,
     expandTree 6 1792 fourRows05[2]!,
     expandTree 6 1792 fourRows05[3]!,
     expandTree 6 1792 fourRows05[4]!,
     expandTree 6 1792 fourRows05[5]!,
     expandTree 6 1792 fourRows05[6]!,
     expandTree 6 1792 fourRows05[7]!,
     expandTree 6 1792 fourRows05[8]!,
     expandTree 6 1792 fourRows05[9]!,
     expandTree 6 1792 fourRows05[10]!,
     expandTree 6 1792 fourRows05[11]!,
     expandTree 6 1792 fourRows05[12]!,
     expandTree 6 1792 fourRows05[13]!,
     expandTree 6 1792 fourRows05[14]!,
     expandTree 6 1792 fourRows05[15]!,
     expandTree 6 1792 fourRows05[16]!,
     expandTree 6 1792 fourRows05[17]!,
     expandTree 6 1792 fourRows05[18]!,
     expandTree 6 1792 fourRows05[19]!,
     expandTree 6 1792 fourRows05[20]!,
     expandTree 6 1792 fourRows05[21]!,
     expandTree 6 1792 fourRows05[22]!,
     expandTree 6 1792 fourRows05[23]!,
     expandTree 6 1792 fourRows05[24]!,
     expandTree 6 1792 fourRows05[25]!,
     expandTree 6 1792 fourRows05[26]!,
     expandTree 6 1792 fourRows05[27]!,
     expandTree 6 1792 fourRows05[28]!,
     expandTree 6 1792 fourRows05[29]!,
     expandTree 6 1792 fourRows05[30]!,
     expandTree 6 1792 fourRows05[31]!]
  rw [expanded05_row00, expanded05_row01, expanded05_row02, expanded05_row03, expanded05_row04, expanded05_row05, expanded05_row06, expanded05_row07, expanded05_row08, expanded05_row09, expanded05_row10, expanded05_row11, expanded05_row12, expanded05_row13, expanded05_row14, expanded05_row15, expanded05_row16, expanded05_row17, expanded05_row18, expanded05_row19, expanded05_row20, expanded05_row21, expanded05_row22, expanded05_row23, expanded05_row24, expanded05_row25, expanded05_row26, expanded05_row27, expanded05_row28, expanded05_row29, expanded05_row30, expanded05_row31]

set_option maxRecDepth 8192 in
private theorem expanded06_row00 : fourWide06[0]! =
    expandTree 6 1792 fourRows06[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row01 : fourWide06[1]! =
    expandTree 6 1792 fourRows06[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row02 : fourWide06[2]! =
    expandTree 6 1792 fourRows06[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row03 : fourWide06[3]! =
    expandTree 6 1792 fourRows06[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row04 : fourWide06[4]! =
    expandTree 6 1792 fourRows06[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row05 : fourWide06[5]! =
    expandTree 6 1792 fourRows06[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row06 : fourWide06[6]! =
    expandTree 6 1792 fourRows06[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row07 : fourWide06[7]! =
    expandTree 6 1792 fourRows06[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row08 : fourWide06[8]! =
    expandTree 6 1792 fourRows06[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row09 : fourWide06[9]! =
    expandTree 6 1792 fourRows06[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row10 : fourWide06[10]! =
    expandTree 6 1792 fourRows06[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row11 : fourWide06[11]! =
    expandTree 6 1792 fourRows06[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row12 : fourWide06[12]! =
    expandTree 6 1792 fourRows06[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row13 : fourWide06[13]! =
    expandTree 6 1792 fourRows06[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row14 : fourWide06[14]! =
    expandTree 6 1792 fourRows06[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row15 : fourWide06[15]! =
    expandTree 6 1792 fourRows06[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row16 : fourWide06[16]! =
    expandTree 6 1792 fourRows06[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row17 : fourWide06[17]! =
    expandTree 6 1792 fourRows06[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row18 : fourWide06[18]! =
    expandTree 6 1792 fourRows06[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row19 : fourWide06[19]! =
    expandTree 6 1792 fourRows06[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row20 : fourWide06[20]! =
    expandTree 6 1792 fourRows06[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row21 : fourWide06[21]! =
    expandTree 6 1792 fourRows06[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row22 : fourWide06[22]! =
    expandTree 6 1792 fourRows06[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row23 : fourWide06[23]! =
    expandTree 6 1792 fourRows06[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row24 : fourWide06[24]! =
    expandTree 6 1792 fourRows06[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row25 : fourWide06[25]! =
    expandTree 6 1792 fourRows06[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row26 : fourWide06[26]! =
    expandTree 6 1792 fourRows06[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row27 : fourWide06[27]! =
    expandTree 6 1792 fourRows06[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row28 : fourWide06[28]! =
    expandTree 6 1792 fourRows06[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row29 : fourWide06[29]! =
    expandTree 6 1792 fourRows06[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row30 : fourWide06[30]! =
    expandTree 6 1792 fourRows06[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded06_row31 : fourWide06[31]! =
    expandTree 6 1792 fourRows06[31]! := by decide +kernel

private theorem expanded06 : fourWide06 =
    fourRows06.map (expandTree 6 1792) := by
  change [fourWide06[0]!,
    fourWide06[1]!,
    fourWide06[2]!,
    fourWide06[3]!,
    fourWide06[4]!,
    fourWide06[5]!,
    fourWide06[6]!,
    fourWide06[7]!,
    fourWide06[8]!,
    fourWide06[9]!,
    fourWide06[10]!,
    fourWide06[11]!,
    fourWide06[12]!,
    fourWide06[13]!,
    fourWide06[14]!,
    fourWide06[15]!,
    fourWide06[16]!,
    fourWide06[17]!,
    fourWide06[18]!,
    fourWide06[19]!,
    fourWide06[20]!,
    fourWide06[21]!,
    fourWide06[22]!,
    fourWide06[23]!,
    fourWide06[24]!,
    fourWide06[25]!,
    fourWide06[26]!,
    fourWide06[27]!,
    fourWide06[28]!,
    fourWide06[29]!,
    fourWide06[30]!,
    fourWide06[31]!] =
    [expandTree 6 1792 fourRows06[0]!,
     expandTree 6 1792 fourRows06[1]!,
     expandTree 6 1792 fourRows06[2]!,
     expandTree 6 1792 fourRows06[3]!,
     expandTree 6 1792 fourRows06[4]!,
     expandTree 6 1792 fourRows06[5]!,
     expandTree 6 1792 fourRows06[6]!,
     expandTree 6 1792 fourRows06[7]!,
     expandTree 6 1792 fourRows06[8]!,
     expandTree 6 1792 fourRows06[9]!,
     expandTree 6 1792 fourRows06[10]!,
     expandTree 6 1792 fourRows06[11]!,
     expandTree 6 1792 fourRows06[12]!,
     expandTree 6 1792 fourRows06[13]!,
     expandTree 6 1792 fourRows06[14]!,
     expandTree 6 1792 fourRows06[15]!,
     expandTree 6 1792 fourRows06[16]!,
     expandTree 6 1792 fourRows06[17]!,
     expandTree 6 1792 fourRows06[18]!,
     expandTree 6 1792 fourRows06[19]!,
     expandTree 6 1792 fourRows06[20]!,
     expandTree 6 1792 fourRows06[21]!,
     expandTree 6 1792 fourRows06[22]!,
     expandTree 6 1792 fourRows06[23]!,
     expandTree 6 1792 fourRows06[24]!,
     expandTree 6 1792 fourRows06[25]!,
     expandTree 6 1792 fourRows06[26]!,
     expandTree 6 1792 fourRows06[27]!,
     expandTree 6 1792 fourRows06[28]!,
     expandTree 6 1792 fourRows06[29]!,
     expandTree 6 1792 fourRows06[30]!,
     expandTree 6 1792 fourRows06[31]!]
  rw [expanded06_row00, expanded06_row01, expanded06_row02, expanded06_row03, expanded06_row04, expanded06_row05, expanded06_row06, expanded06_row07, expanded06_row08, expanded06_row09, expanded06_row10, expanded06_row11, expanded06_row12, expanded06_row13, expanded06_row14, expanded06_row15, expanded06_row16, expanded06_row17, expanded06_row18, expanded06_row19, expanded06_row20, expanded06_row21, expanded06_row22, expanded06_row23, expanded06_row24, expanded06_row25, expanded06_row26, expanded06_row27, expanded06_row28, expanded06_row29, expanded06_row30, expanded06_row31]

set_option maxRecDepth 8192 in
private theorem expanded07_row00 : fourWide07[0]! =
    expandTree 6 1792 fourRows07[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row01 : fourWide07[1]! =
    expandTree 6 1792 fourRows07[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row02 : fourWide07[2]! =
    expandTree 6 1792 fourRows07[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row03 : fourWide07[3]! =
    expandTree 6 1792 fourRows07[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row04 : fourWide07[4]! =
    expandTree 6 1792 fourRows07[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row05 : fourWide07[5]! =
    expandTree 6 1792 fourRows07[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row06 : fourWide07[6]! =
    expandTree 6 1792 fourRows07[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row07 : fourWide07[7]! =
    expandTree 6 1792 fourRows07[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row08 : fourWide07[8]! =
    expandTree 6 1792 fourRows07[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row09 : fourWide07[9]! =
    expandTree 6 1792 fourRows07[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row10 : fourWide07[10]! =
    expandTree 6 1792 fourRows07[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row11 : fourWide07[11]! =
    expandTree 6 1792 fourRows07[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row12 : fourWide07[12]! =
    expandTree 6 1792 fourRows07[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row13 : fourWide07[13]! =
    expandTree 6 1792 fourRows07[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row14 : fourWide07[14]! =
    expandTree 6 1792 fourRows07[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row15 : fourWide07[15]! =
    expandTree 6 1792 fourRows07[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row16 : fourWide07[16]! =
    expandTree 6 1792 fourRows07[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row17 : fourWide07[17]! =
    expandTree 6 1792 fourRows07[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row18 : fourWide07[18]! =
    expandTree 6 1792 fourRows07[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row19 : fourWide07[19]! =
    expandTree 6 1792 fourRows07[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row20 : fourWide07[20]! =
    expandTree 6 1792 fourRows07[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row21 : fourWide07[21]! =
    expandTree 6 1792 fourRows07[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row22 : fourWide07[22]! =
    expandTree 6 1792 fourRows07[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row23 : fourWide07[23]! =
    expandTree 6 1792 fourRows07[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row24 : fourWide07[24]! =
    expandTree 6 1792 fourRows07[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row25 : fourWide07[25]! =
    expandTree 6 1792 fourRows07[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row26 : fourWide07[26]! =
    expandTree 6 1792 fourRows07[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row27 : fourWide07[27]! =
    expandTree 6 1792 fourRows07[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row28 : fourWide07[28]! =
    expandTree 6 1792 fourRows07[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row29 : fourWide07[29]! =
    expandTree 6 1792 fourRows07[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row30 : fourWide07[30]! =
    expandTree 6 1792 fourRows07[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded07_row31 : fourWide07[31]! =
    expandTree 6 1792 fourRows07[31]! := by decide +kernel

private theorem expanded07 : fourWide07 =
    fourRows07.map (expandTree 6 1792) := by
  change [fourWide07[0]!,
    fourWide07[1]!,
    fourWide07[2]!,
    fourWide07[3]!,
    fourWide07[4]!,
    fourWide07[5]!,
    fourWide07[6]!,
    fourWide07[7]!,
    fourWide07[8]!,
    fourWide07[9]!,
    fourWide07[10]!,
    fourWide07[11]!,
    fourWide07[12]!,
    fourWide07[13]!,
    fourWide07[14]!,
    fourWide07[15]!,
    fourWide07[16]!,
    fourWide07[17]!,
    fourWide07[18]!,
    fourWide07[19]!,
    fourWide07[20]!,
    fourWide07[21]!,
    fourWide07[22]!,
    fourWide07[23]!,
    fourWide07[24]!,
    fourWide07[25]!,
    fourWide07[26]!,
    fourWide07[27]!,
    fourWide07[28]!,
    fourWide07[29]!,
    fourWide07[30]!,
    fourWide07[31]!] =
    [expandTree 6 1792 fourRows07[0]!,
     expandTree 6 1792 fourRows07[1]!,
     expandTree 6 1792 fourRows07[2]!,
     expandTree 6 1792 fourRows07[3]!,
     expandTree 6 1792 fourRows07[4]!,
     expandTree 6 1792 fourRows07[5]!,
     expandTree 6 1792 fourRows07[6]!,
     expandTree 6 1792 fourRows07[7]!,
     expandTree 6 1792 fourRows07[8]!,
     expandTree 6 1792 fourRows07[9]!,
     expandTree 6 1792 fourRows07[10]!,
     expandTree 6 1792 fourRows07[11]!,
     expandTree 6 1792 fourRows07[12]!,
     expandTree 6 1792 fourRows07[13]!,
     expandTree 6 1792 fourRows07[14]!,
     expandTree 6 1792 fourRows07[15]!,
     expandTree 6 1792 fourRows07[16]!,
     expandTree 6 1792 fourRows07[17]!,
     expandTree 6 1792 fourRows07[18]!,
     expandTree 6 1792 fourRows07[19]!,
     expandTree 6 1792 fourRows07[20]!,
     expandTree 6 1792 fourRows07[21]!,
     expandTree 6 1792 fourRows07[22]!,
     expandTree 6 1792 fourRows07[23]!,
     expandTree 6 1792 fourRows07[24]!,
     expandTree 6 1792 fourRows07[25]!,
     expandTree 6 1792 fourRows07[26]!,
     expandTree 6 1792 fourRows07[27]!,
     expandTree 6 1792 fourRows07[28]!,
     expandTree 6 1792 fourRows07[29]!,
     expandTree 6 1792 fourRows07[30]!,
     expandTree 6 1792 fourRows07[31]!]
  rw [expanded07_row00, expanded07_row01, expanded07_row02, expanded07_row03, expanded07_row04, expanded07_row05, expanded07_row06, expanded07_row07, expanded07_row08, expanded07_row09, expanded07_row10, expanded07_row11, expanded07_row12, expanded07_row13, expanded07_row14, expanded07_row15, expanded07_row16, expanded07_row17, expanded07_row18, expanded07_row19, expanded07_row20, expanded07_row21, expanded07_row22, expanded07_row23, expanded07_row24, expanded07_row25, expanded07_row26, expanded07_row27, expanded07_row28, expanded07_row29, expanded07_row30, expanded07_row31]

set_option maxRecDepth 8192 in
private theorem expanded08_row00 : fourWide08[0]! =
    expandTree 6 1792 fourRows08[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row01 : fourWide08[1]! =
    expandTree 6 1792 fourRows08[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row02 : fourWide08[2]! =
    expandTree 6 1792 fourRows08[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row03 : fourWide08[3]! =
    expandTree 6 1792 fourRows08[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row04 : fourWide08[4]! =
    expandTree 6 1792 fourRows08[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row05 : fourWide08[5]! =
    expandTree 6 1792 fourRows08[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row06 : fourWide08[6]! =
    expandTree 6 1792 fourRows08[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row07 : fourWide08[7]! =
    expandTree 6 1792 fourRows08[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row08 : fourWide08[8]! =
    expandTree 6 1792 fourRows08[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row09 : fourWide08[9]! =
    expandTree 6 1792 fourRows08[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row10 : fourWide08[10]! =
    expandTree 6 1792 fourRows08[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row11 : fourWide08[11]! =
    expandTree 6 1792 fourRows08[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row12 : fourWide08[12]! =
    expandTree 6 1792 fourRows08[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row13 : fourWide08[13]! =
    expandTree 6 1792 fourRows08[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row14 : fourWide08[14]! =
    expandTree 6 1792 fourRows08[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row15 : fourWide08[15]! =
    expandTree 6 1792 fourRows08[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row16 : fourWide08[16]! =
    expandTree 6 1792 fourRows08[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row17 : fourWide08[17]! =
    expandTree 6 1792 fourRows08[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row18 : fourWide08[18]! =
    expandTree 6 1792 fourRows08[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row19 : fourWide08[19]! =
    expandTree 6 1792 fourRows08[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row20 : fourWide08[20]! =
    expandTree 6 1792 fourRows08[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row21 : fourWide08[21]! =
    expandTree 6 1792 fourRows08[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row22 : fourWide08[22]! =
    expandTree 6 1792 fourRows08[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row23 : fourWide08[23]! =
    expandTree 6 1792 fourRows08[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row24 : fourWide08[24]! =
    expandTree 6 1792 fourRows08[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row25 : fourWide08[25]! =
    expandTree 6 1792 fourRows08[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row26 : fourWide08[26]! =
    expandTree 6 1792 fourRows08[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row27 : fourWide08[27]! =
    expandTree 6 1792 fourRows08[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row28 : fourWide08[28]! =
    expandTree 6 1792 fourRows08[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row29 : fourWide08[29]! =
    expandTree 6 1792 fourRows08[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row30 : fourWide08[30]! =
    expandTree 6 1792 fourRows08[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded08_row31 : fourWide08[31]! =
    expandTree 6 1792 fourRows08[31]! := by decide +kernel

private theorem expanded08 : fourWide08 =
    fourRows08.map (expandTree 6 1792) := by
  change [fourWide08[0]!,
    fourWide08[1]!,
    fourWide08[2]!,
    fourWide08[3]!,
    fourWide08[4]!,
    fourWide08[5]!,
    fourWide08[6]!,
    fourWide08[7]!,
    fourWide08[8]!,
    fourWide08[9]!,
    fourWide08[10]!,
    fourWide08[11]!,
    fourWide08[12]!,
    fourWide08[13]!,
    fourWide08[14]!,
    fourWide08[15]!,
    fourWide08[16]!,
    fourWide08[17]!,
    fourWide08[18]!,
    fourWide08[19]!,
    fourWide08[20]!,
    fourWide08[21]!,
    fourWide08[22]!,
    fourWide08[23]!,
    fourWide08[24]!,
    fourWide08[25]!,
    fourWide08[26]!,
    fourWide08[27]!,
    fourWide08[28]!,
    fourWide08[29]!,
    fourWide08[30]!,
    fourWide08[31]!] =
    [expandTree 6 1792 fourRows08[0]!,
     expandTree 6 1792 fourRows08[1]!,
     expandTree 6 1792 fourRows08[2]!,
     expandTree 6 1792 fourRows08[3]!,
     expandTree 6 1792 fourRows08[4]!,
     expandTree 6 1792 fourRows08[5]!,
     expandTree 6 1792 fourRows08[6]!,
     expandTree 6 1792 fourRows08[7]!,
     expandTree 6 1792 fourRows08[8]!,
     expandTree 6 1792 fourRows08[9]!,
     expandTree 6 1792 fourRows08[10]!,
     expandTree 6 1792 fourRows08[11]!,
     expandTree 6 1792 fourRows08[12]!,
     expandTree 6 1792 fourRows08[13]!,
     expandTree 6 1792 fourRows08[14]!,
     expandTree 6 1792 fourRows08[15]!,
     expandTree 6 1792 fourRows08[16]!,
     expandTree 6 1792 fourRows08[17]!,
     expandTree 6 1792 fourRows08[18]!,
     expandTree 6 1792 fourRows08[19]!,
     expandTree 6 1792 fourRows08[20]!,
     expandTree 6 1792 fourRows08[21]!,
     expandTree 6 1792 fourRows08[22]!,
     expandTree 6 1792 fourRows08[23]!,
     expandTree 6 1792 fourRows08[24]!,
     expandTree 6 1792 fourRows08[25]!,
     expandTree 6 1792 fourRows08[26]!,
     expandTree 6 1792 fourRows08[27]!,
     expandTree 6 1792 fourRows08[28]!,
     expandTree 6 1792 fourRows08[29]!,
     expandTree 6 1792 fourRows08[30]!,
     expandTree 6 1792 fourRows08[31]!]
  rw [expanded08_row00, expanded08_row01, expanded08_row02, expanded08_row03, expanded08_row04, expanded08_row05, expanded08_row06, expanded08_row07, expanded08_row08, expanded08_row09, expanded08_row10, expanded08_row11, expanded08_row12, expanded08_row13, expanded08_row14, expanded08_row15, expanded08_row16, expanded08_row17, expanded08_row18, expanded08_row19, expanded08_row20, expanded08_row21, expanded08_row22, expanded08_row23, expanded08_row24, expanded08_row25, expanded08_row26, expanded08_row27, expanded08_row28, expanded08_row29, expanded08_row30, expanded08_row31]

set_option maxRecDepth 8192 in
private theorem expanded09_row00 : fourWide09[0]! =
    expandTree 6 1792 fourRows09[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row01 : fourWide09[1]! =
    expandTree 6 1792 fourRows09[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row02 : fourWide09[2]! =
    expandTree 6 1792 fourRows09[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row03 : fourWide09[3]! =
    expandTree 6 1792 fourRows09[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row04 : fourWide09[4]! =
    expandTree 6 1792 fourRows09[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row05 : fourWide09[5]! =
    expandTree 6 1792 fourRows09[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row06 : fourWide09[6]! =
    expandTree 6 1792 fourRows09[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row07 : fourWide09[7]! =
    expandTree 6 1792 fourRows09[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row08 : fourWide09[8]! =
    expandTree 6 1792 fourRows09[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row09 : fourWide09[9]! =
    expandTree 6 1792 fourRows09[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row10 : fourWide09[10]! =
    expandTree 6 1792 fourRows09[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row11 : fourWide09[11]! =
    expandTree 6 1792 fourRows09[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row12 : fourWide09[12]! =
    expandTree 6 1792 fourRows09[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row13 : fourWide09[13]! =
    expandTree 6 1792 fourRows09[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row14 : fourWide09[14]! =
    expandTree 6 1792 fourRows09[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row15 : fourWide09[15]! =
    expandTree 6 1792 fourRows09[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row16 : fourWide09[16]! =
    expandTree 6 1792 fourRows09[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row17 : fourWide09[17]! =
    expandTree 6 1792 fourRows09[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row18 : fourWide09[18]! =
    expandTree 6 1792 fourRows09[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row19 : fourWide09[19]! =
    expandTree 6 1792 fourRows09[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row20 : fourWide09[20]! =
    expandTree 6 1792 fourRows09[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row21 : fourWide09[21]! =
    expandTree 6 1792 fourRows09[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row22 : fourWide09[22]! =
    expandTree 6 1792 fourRows09[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row23 : fourWide09[23]! =
    expandTree 6 1792 fourRows09[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row24 : fourWide09[24]! =
    expandTree 6 1792 fourRows09[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row25 : fourWide09[25]! =
    expandTree 6 1792 fourRows09[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row26 : fourWide09[26]! =
    expandTree 6 1792 fourRows09[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row27 : fourWide09[27]! =
    expandTree 6 1792 fourRows09[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row28 : fourWide09[28]! =
    expandTree 6 1792 fourRows09[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row29 : fourWide09[29]! =
    expandTree 6 1792 fourRows09[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row30 : fourWide09[30]! =
    expandTree 6 1792 fourRows09[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded09_row31 : fourWide09[31]! =
    expandTree 6 1792 fourRows09[31]! := by decide +kernel

private theorem expanded09 : fourWide09 =
    fourRows09.map (expandTree 6 1792) := by
  change [fourWide09[0]!,
    fourWide09[1]!,
    fourWide09[2]!,
    fourWide09[3]!,
    fourWide09[4]!,
    fourWide09[5]!,
    fourWide09[6]!,
    fourWide09[7]!,
    fourWide09[8]!,
    fourWide09[9]!,
    fourWide09[10]!,
    fourWide09[11]!,
    fourWide09[12]!,
    fourWide09[13]!,
    fourWide09[14]!,
    fourWide09[15]!,
    fourWide09[16]!,
    fourWide09[17]!,
    fourWide09[18]!,
    fourWide09[19]!,
    fourWide09[20]!,
    fourWide09[21]!,
    fourWide09[22]!,
    fourWide09[23]!,
    fourWide09[24]!,
    fourWide09[25]!,
    fourWide09[26]!,
    fourWide09[27]!,
    fourWide09[28]!,
    fourWide09[29]!,
    fourWide09[30]!,
    fourWide09[31]!] =
    [expandTree 6 1792 fourRows09[0]!,
     expandTree 6 1792 fourRows09[1]!,
     expandTree 6 1792 fourRows09[2]!,
     expandTree 6 1792 fourRows09[3]!,
     expandTree 6 1792 fourRows09[4]!,
     expandTree 6 1792 fourRows09[5]!,
     expandTree 6 1792 fourRows09[6]!,
     expandTree 6 1792 fourRows09[7]!,
     expandTree 6 1792 fourRows09[8]!,
     expandTree 6 1792 fourRows09[9]!,
     expandTree 6 1792 fourRows09[10]!,
     expandTree 6 1792 fourRows09[11]!,
     expandTree 6 1792 fourRows09[12]!,
     expandTree 6 1792 fourRows09[13]!,
     expandTree 6 1792 fourRows09[14]!,
     expandTree 6 1792 fourRows09[15]!,
     expandTree 6 1792 fourRows09[16]!,
     expandTree 6 1792 fourRows09[17]!,
     expandTree 6 1792 fourRows09[18]!,
     expandTree 6 1792 fourRows09[19]!,
     expandTree 6 1792 fourRows09[20]!,
     expandTree 6 1792 fourRows09[21]!,
     expandTree 6 1792 fourRows09[22]!,
     expandTree 6 1792 fourRows09[23]!,
     expandTree 6 1792 fourRows09[24]!,
     expandTree 6 1792 fourRows09[25]!,
     expandTree 6 1792 fourRows09[26]!,
     expandTree 6 1792 fourRows09[27]!,
     expandTree 6 1792 fourRows09[28]!,
     expandTree 6 1792 fourRows09[29]!,
     expandTree 6 1792 fourRows09[30]!,
     expandTree 6 1792 fourRows09[31]!]
  rw [expanded09_row00, expanded09_row01, expanded09_row02, expanded09_row03, expanded09_row04, expanded09_row05, expanded09_row06, expanded09_row07, expanded09_row08, expanded09_row09, expanded09_row10, expanded09_row11, expanded09_row12, expanded09_row13, expanded09_row14, expanded09_row15, expanded09_row16, expanded09_row17, expanded09_row18, expanded09_row19, expanded09_row20, expanded09_row21, expanded09_row22, expanded09_row23, expanded09_row24, expanded09_row25, expanded09_row26, expanded09_row27, expanded09_row28, expanded09_row29, expanded09_row30, expanded09_row31]

set_option maxRecDepth 8192 in
private theorem expanded10_row00 : fourWide10[0]! =
    expandTree 6 1792 fourRows10[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row01 : fourWide10[1]! =
    expandTree 6 1792 fourRows10[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row02 : fourWide10[2]! =
    expandTree 6 1792 fourRows10[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row03 : fourWide10[3]! =
    expandTree 6 1792 fourRows10[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row04 : fourWide10[4]! =
    expandTree 6 1792 fourRows10[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row05 : fourWide10[5]! =
    expandTree 6 1792 fourRows10[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row06 : fourWide10[6]! =
    expandTree 6 1792 fourRows10[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row07 : fourWide10[7]! =
    expandTree 6 1792 fourRows10[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row08 : fourWide10[8]! =
    expandTree 6 1792 fourRows10[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row09 : fourWide10[9]! =
    expandTree 6 1792 fourRows10[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row10 : fourWide10[10]! =
    expandTree 6 1792 fourRows10[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row11 : fourWide10[11]! =
    expandTree 6 1792 fourRows10[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row12 : fourWide10[12]! =
    expandTree 6 1792 fourRows10[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row13 : fourWide10[13]! =
    expandTree 6 1792 fourRows10[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row14 : fourWide10[14]! =
    expandTree 6 1792 fourRows10[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row15 : fourWide10[15]! =
    expandTree 6 1792 fourRows10[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row16 : fourWide10[16]! =
    expandTree 6 1792 fourRows10[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row17 : fourWide10[17]! =
    expandTree 6 1792 fourRows10[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row18 : fourWide10[18]! =
    expandTree 6 1792 fourRows10[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row19 : fourWide10[19]! =
    expandTree 6 1792 fourRows10[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row20 : fourWide10[20]! =
    expandTree 6 1792 fourRows10[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row21 : fourWide10[21]! =
    expandTree 6 1792 fourRows10[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row22 : fourWide10[22]! =
    expandTree 6 1792 fourRows10[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row23 : fourWide10[23]! =
    expandTree 6 1792 fourRows10[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row24 : fourWide10[24]! =
    expandTree 6 1792 fourRows10[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row25 : fourWide10[25]! =
    expandTree 6 1792 fourRows10[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row26 : fourWide10[26]! =
    expandTree 6 1792 fourRows10[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row27 : fourWide10[27]! =
    expandTree 6 1792 fourRows10[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row28 : fourWide10[28]! =
    expandTree 6 1792 fourRows10[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row29 : fourWide10[29]! =
    expandTree 6 1792 fourRows10[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row30 : fourWide10[30]! =
    expandTree 6 1792 fourRows10[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded10_row31 : fourWide10[31]! =
    expandTree 6 1792 fourRows10[31]! := by decide +kernel

private theorem expanded10 : fourWide10 =
    fourRows10.map (expandTree 6 1792) := by
  change [fourWide10[0]!,
    fourWide10[1]!,
    fourWide10[2]!,
    fourWide10[3]!,
    fourWide10[4]!,
    fourWide10[5]!,
    fourWide10[6]!,
    fourWide10[7]!,
    fourWide10[8]!,
    fourWide10[9]!,
    fourWide10[10]!,
    fourWide10[11]!,
    fourWide10[12]!,
    fourWide10[13]!,
    fourWide10[14]!,
    fourWide10[15]!,
    fourWide10[16]!,
    fourWide10[17]!,
    fourWide10[18]!,
    fourWide10[19]!,
    fourWide10[20]!,
    fourWide10[21]!,
    fourWide10[22]!,
    fourWide10[23]!,
    fourWide10[24]!,
    fourWide10[25]!,
    fourWide10[26]!,
    fourWide10[27]!,
    fourWide10[28]!,
    fourWide10[29]!,
    fourWide10[30]!,
    fourWide10[31]!] =
    [expandTree 6 1792 fourRows10[0]!,
     expandTree 6 1792 fourRows10[1]!,
     expandTree 6 1792 fourRows10[2]!,
     expandTree 6 1792 fourRows10[3]!,
     expandTree 6 1792 fourRows10[4]!,
     expandTree 6 1792 fourRows10[5]!,
     expandTree 6 1792 fourRows10[6]!,
     expandTree 6 1792 fourRows10[7]!,
     expandTree 6 1792 fourRows10[8]!,
     expandTree 6 1792 fourRows10[9]!,
     expandTree 6 1792 fourRows10[10]!,
     expandTree 6 1792 fourRows10[11]!,
     expandTree 6 1792 fourRows10[12]!,
     expandTree 6 1792 fourRows10[13]!,
     expandTree 6 1792 fourRows10[14]!,
     expandTree 6 1792 fourRows10[15]!,
     expandTree 6 1792 fourRows10[16]!,
     expandTree 6 1792 fourRows10[17]!,
     expandTree 6 1792 fourRows10[18]!,
     expandTree 6 1792 fourRows10[19]!,
     expandTree 6 1792 fourRows10[20]!,
     expandTree 6 1792 fourRows10[21]!,
     expandTree 6 1792 fourRows10[22]!,
     expandTree 6 1792 fourRows10[23]!,
     expandTree 6 1792 fourRows10[24]!,
     expandTree 6 1792 fourRows10[25]!,
     expandTree 6 1792 fourRows10[26]!,
     expandTree 6 1792 fourRows10[27]!,
     expandTree 6 1792 fourRows10[28]!,
     expandTree 6 1792 fourRows10[29]!,
     expandTree 6 1792 fourRows10[30]!,
     expandTree 6 1792 fourRows10[31]!]
  rw [expanded10_row00, expanded10_row01, expanded10_row02, expanded10_row03, expanded10_row04, expanded10_row05, expanded10_row06, expanded10_row07, expanded10_row08, expanded10_row09, expanded10_row10, expanded10_row11, expanded10_row12, expanded10_row13, expanded10_row14, expanded10_row15, expanded10_row16, expanded10_row17, expanded10_row18, expanded10_row19, expanded10_row20, expanded10_row21, expanded10_row22, expanded10_row23, expanded10_row24, expanded10_row25, expanded10_row26, expanded10_row27, expanded10_row28, expanded10_row29, expanded10_row30, expanded10_row31]

set_option maxRecDepth 8192 in
private theorem expanded11_row00 : fourWide11[0]! =
    expandTree 6 1792 fourRows11[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row01 : fourWide11[1]! =
    expandTree 6 1792 fourRows11[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row02 : fourWide11[2]! =
    expandTree 6 1792 fourRows11[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row03 : fourWide11[3]! =
    expandTree 6 1792 fourRows11[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row04 : fourWide11[4]! =
    expandTree 6 1792 fourRows11[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row05 : fourWide11[5]! =
    expandTree 6 1792 fourRows11[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row06 : fourWide11[6]! =
    expandTree 6 1792 fourRows11[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row07 : fourWide11[7]! =
    expandTree 6 1792 fourRows11[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row08 : fourWide11[8]! =
    expandTree 6 1792 fourRows11[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row09 : fourWide11[9]! =
    expandTree 6 1792 fourRows11[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row10 : fourWide11[10]! =
    expandTree 6 1792 fourRows11[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row11 : fourWide11[11]! =
    expandTree 6 1792 fourRows11[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row12 : fourWide11[12]! =
    expandTree 6 1792 fourRows11[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row13 : fourWide11[13]! =
    expandTree 6 1792 fourRows11[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row14 : fourWide11[14]! =
    expandTree 6 1792 fourRows11[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row15 : fourWide11[15]! =
    expandTree 6 1792 fourRows11[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row16 : fourWide11[16]! =
    expandTree 6 1792 fourRows11[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row17 : fourWide11[17]! =
    expandTree 6 1792 fourRows11[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row18 : fourWide11[18]! =
    expandTree 6 1792 fourRows11[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row19 : fourWide11[19]! =
    expandTree 6 1792 fourRows11[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row20 : fourWide11[20]! =
    expandTree 6 1792 fourRows11[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row21 : fourWide11[21]! =
    expandTree 6 1792 fourRows11[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row22 : fourWide11[22]! =
    expandTree 6 1792 fourRows11[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row23 : fourWide11[23]! =
    expandTree 6 1792 fourRows11[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row24 : fourWide11[24]! =
    expandTree 6 1792 fourRows11[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row25 : fourWide11[25]! =
    expandTree 6 1792 fourRows11[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row26 : fourWide11[26]! =
    expandTree 6 1792 fourRows11[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row27 : fourWide11[27]! =
    expandTree 6 1792 fourRows11[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row28 : fourWide11[28]! =
    expandTree 6 1792 fourRows11[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row29 : fourWide11[29]! =
    expandTree 6 1792 fourRows11[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row30 : fourWide11[30]! =
    expandTree 6 1792 fourRows11[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded11_row31 : fourWide11[31]! =
    expandTree 6 1792 fourRows11[31]! := by decide +kernel

private theorem expanded11 : fourWide11 =
    fourRows11.map (expandTree 6 1792) := by
  change [fourWide11[0]!,
    fourWide11[1]!,
    fourWide11[2]!,
    fourWide11[3]!,
    fourWide11[4]!,
    fourWide11[5]!,
    fourWide11[6]!,
    fourWide11[7]!,
    fourWide11[8]!,
    fourWide11[9]!,
    fourWide11[10]!,
    fourWide11[11]!,
    fourWide11[12]!,
    fourWide11[13]!,
    fourWide11[14]!,
    fourWide11[15]!,
    fourWide11[16]!,
    fourWide11[17]!,
    fourWide11[18]!,
    fourWide11[19]!,
    fourWide11[20]!,
    fourWide11[21]!,
    fourWide11[22]!,
    fourWide11[23]!,
    fourWide11[24]!,
    fourWide11[25]!,
    fourWide11[26]!,
    fourWide11[27]!,
    fourWide11[28]!,
    fourWide11[29]!,
    fourWide11[30]!,
    fourWide11[31]!] =
    [expandTree 6 1792 fourRows11[0]!,
     expandTree 6 1792 fourRows11[1]!,
     expandTree 6 1792 fourRows11[2]!,
     expandTree 6 1792 fourRows11[3]!,
     expandTree 6 1792 fourRows11[4]!,
     expandTree 6 1792 fourRows11[5]!,
     expandTree 6 1792 fourRows11[6]!,
     expandTree 6 1792 fourRows11[7]!,
     expandTree 6 1792 fourRows11[8]!,
     expandTree 6 1792 fourRows11[9]!,
     expandTree 6 1792 fourRows11[10]!,
     expandTree 6 1792 fourRows11[11]!,
     expandTree 6 1792 fourRows11[12]!,
     expandTree 6 1792 fourRows11[13]!,
     expandTree 6 1792 fourRows11[14]!,
     expandTree 6 1792 fourRows11[15]!,
     expandTree 6 1792 fourRows11[16]!,
     expandTree 6 1792 fourRows11[17]!,
     expandTree 6 1792 fourRows11[18]!,
     expandTree 6 1792 fourRows11[19]!,
     expandTree 6 1792 fourRows11[20]!,
     expandTree 6 1792 fourRows11[21]!,
     expandTree 6 1792 fourRows11[22]!,
     expandTree 6 1792 fourRows11[23]!,
     expandTree 6 1792 fourRows11[24]!,
     expandTree 6 1792 fourRows11[25]!,
     expandTree 6 1792 fourRows11[26]!,
     expandTree 6 1792 fourRows11[27]!,
     expandTree 6 1792 fourRows11[28]!,
     expandTree 6 1792 fourRows11[29]!,
     expandTree 6 1792 fourRows11[30]!,
     expandTree 6 1792 fourRows11[31]!]
  rw [expanded11_row00, expanded11_row01, expanded11_row02, expanded11_row03, expanded11_row04, expanded11_row05, expanded11_row06, expanded11_row07, expanded11_row08, expanded11_row09, expanded11_row10, expanded11_row11, expanded11_row12, expanded11_row13, expanded11_row14, expanded11_row15, expanded11_row16, expanded11_row17, expanded11_row18, expanded11_row19, expanded11_row20, expanded11_row21, expanded11_row22, expanded11_row23, expanded11_row24, expanded11_row25, expanded11_row26, expanded11_row27, expanded11_row28, expanded11_row29, expanded11_row30, expanded11_row31]

set_option maxRecDepth 8192 in
private theorem expanded12_row00 : fourWide12[0]! =
    expandTree 6 1792 fourRows12[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row01 : fourWide12[1]! =
    expandTree 6 1792 fourRows12[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row02 : fourWide12[2]! =
    expandTree 6 1792 fourRows12[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row03 : fourWide12[3]! =
    expandTree 6 1792 fourRows12[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row04 : fourWide12[4]! =
    expandTree 6 1792 fourRows12[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row05 : fourWide12[5]! =
    expandTree 6 1792 fourRows12[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row06 : fourWide12[6]! =
    expandTree 6 1792 fourRows12[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row07 : fourWide12[7]! =
    expandTree 6 1792 fourRows12[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row08 : fourWide12[8]! =
    expandTree 6 1792 fourRows12[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row09 : fourWide12[9]! =
    expandTree 6 1792 fourRows12[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row10 : fourWide12[10]! =
    expandTree 6 1792 fourRows12[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row11 : fourWide12[11]! =
    expandTree 6 1792 fourRows12[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row12 : fourWide12[12]! =
    expandTree 6 1792 fourRows12[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row13 : fourWide12[13]! =
    expandTree 6 1792 fourRows12[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row14 : fourWide12[14]! =
    expandTree 6 1792 fourRows12[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row15 : fourWide12[15]! =
    expandTree 6 1792 fourRows12[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row16 : fourWide12[16]! =
    expandTree 6 1792 fourRows12[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row17 : fourWide12[17]! =
    expandTree 6 1792 fourRows12[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row18 : fourWide12[18]! =
    expandTree 6 1792 fourRows12[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row19 : fourWide12[19]! =
    expandTree 6 1792 fourRows12[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row20 : fourWide12[20]! =
    expandTree 6 1792 fourRows12[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row21 : fourWide12[21]! =
    expandTree 6 1792 fourRows12[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row22 : fourWide12[22]! =
    expandTree 6 1792 fourRows12[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row23 : fourWide12[23]! =
    expandTree 6 1792 fourRows12[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row24 : fourWide12[24]! =
    expandTree 6 1792 fourRows12[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row25 : fourWide12[25]! =
    expandTree 6 1792 fourRows12[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row26 : fourWide12[26]! =
    expandTree 6 1792 fourRows12[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row27 : fourWide12[27]! =
    expandTree 6 1792 fourRows12[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row28 : fourWide12[28]! =
    expandTree 6 1792 fourRows12[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row29 : fourWide12[29]! =
    expandTree 6 1792 fourRows12[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row30 : fourWide12[30]! =
    expandTree 6 1792 fourRows12[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded12_row31 : fourWide12[31]! =
    expandTree 6 1792 fourRows12[31]! := by decide +kernel

private theorem expanded12 : fourWide12 =
    fourRows12.map (expandTree 6 1792) := by
  change [fourWide12[0]!,
    fourWide12[1]!,
    fourWide12[2]!,
    fourWide12[3]!,
    fourWide12[4]!,
    fourWide12[5]!,
    fourWide12[6]!,
    fourWide12[7]!,
    fourWide12[8]!,
    fourWide12[9]!,
    fourWide12[10]!,
    fourWide12[11]!,
    fourWide12[12]!,
    fourWide12[13]!,
    fourWide12[14]!,
    fourWide12[15]!,
    fourWide12[16]!,
    fourWide12[17]!,
    fourWide12[18]!,
    fourWide12[19]!,
    fourWide12[20]!,
    fourWide12[21]!,
    fourWide12[22]!,
    fourWide12[23]!,
    fourWide12[24]!,
    fourWide12[25]!,
    fourWide12[26]!,
    fourWide12[27]!,
    fourWide12[28]!,
    fourWide12[29]!,
    fourWide12[30]!,
    fourWide12[31]!] =
    [expandTree 6 1792 fourRows12[0]!,
     expandTree 6 1792 fourRows12[1]!,
     expandTree 6 1792 fourRows12[2]!,
     expandTree 6 1792 fourRows12[3]!,
     expandTree 6 1792 fourRows12[4]!,
     expandTree 6 1792 fourRows12[5]!,
     expandTree 6 1792 fourRows12[6]!,
     expandTree 6 1792 fourRows12[7]!,
     expandTree 6 1792 fourRows12[8]!,
     expandTree 6 1792 fourRows12[9]!,
     expandTree 6 1792 fourRows12[10]!,
     expandTree 6 1792 fourRows12[11]!,
     expandTree 6 1792 fourRows12[12]!,
     expandTree 6 1792 fourRows12[13]!,
     expandTree 6 1792 fourRows12[14]!,
     expandTree 6 1792 fourRows12[15]!,
     expandTree 6 1792 fourRows12[16]!,
     expandTree 6 1792 fourRows12[17]!,
     expandTree 6 1792 fourRows12[18]!,
     expandTree 6 1792 fourRows12[19]!,
     expandTree 6 1792 fourRows12[20]!,
     expandTree 6 1792 fourRows12[21]!,
     expandTree 6 1792 fourRows12[22]!,
     expandTree 6 1792 fourRows12[23]!,
     expandTree 6 1792 fourRows12[24]!,
     expandTree 6 1792 fourRows12[25]!,
     expandTree 6 1792 fourRows12[26]!,
     expandTree 6 1792 fourRows12[27]!,
     expandTree 6 1792 fourRows12[28]!,
     expandTree 6 1792 fourRows12[29]!,
     expandTree 6 1792 fourRows12[30]!,
     expandTree 6 1792 fourRows12[31]!]
  rw [expanded12_row00, expanded12_row01, expanded12_row02, expanded12_row03, expanded12_row04, expanded12_row05, expanded12_row06, expanded12_row07, expanded12_row08, expanded12_row09, expanded12_row10, expanded12_row11, expanded12_row12, expanded12_row13, expanded12_row14, expanded12_row15, expanded12_row16, expanded12_row17, expanded12_row18, expanded12_row19, expanded12_row20, expanded12_row21, expanded12_row22, expanded12_row23, expanded12_row24, expanded12_row25, expanded12_row26, expanded12_row27, expanded12_row28, expanded12_row29, expanded12_row30, expanded12_row31]

set_option maxRecDepth 8192 in
private theorem expanded13_row00 : fourWide13[0]! =
    expandTree 6 1792 fourRows13[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row01 : fourWide13[1]! =
    expandTree 6 1792 fourRows13[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row02 : fourWide13[2]! =
    expandTree 6 1792 fourRows13[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row03 : fourWide13[3]! =
    expandTree 6 1792 fourRows13[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row04 : fourWide13[4]! =
    expandTree 6 1792 fourRows13[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row05 : fourWide13[5]! =
    expandTree 6 1792 fourRows13[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row06 : fourWide13[6]! =
    expandTree 6 1792 fourRows13[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row07 : fourWide13[7]! =
    expandTree 6 1792 fourRows13[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row08 : fourWide13[8]! =
    expandTree 6 1792 fourRows13[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row09 : fourWide13[9]! =
    expandTree 6 1792 fourRows13[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row10 : fourWide13[10]! =
    expandTree 6 1792 fourRows13[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row11 : fourWide13[11]! =
    expandTree 6 1792 fourRows13[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row12 : fourWide13[12]! =
    expandTree 6 1792 fourRows13[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row13 : fourWide13[13]! =
    expandTree 6 1792 fourRows13[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row14 : fourWide13[14]! =
    expandTree 6 1792 fourRows13[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row15 : fourWide13[15]! =
    expandTree 6 1792 fourRows13[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row16 : fourWide13[16]! =
    expandTree 6 1792 fourRows13[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row17 : fourWide13[17]! =
    expandTree 6 1792 fourRows13[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row18 : fourWide13[18]! =
    expandTree 6 1792 fourRows13[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row19 : fourWide13[19]! =
    expandTree 6 1792 fourRows13[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row20 : fourWide13[20]! =
    expandTree 6 1792 fourRows13[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row21 : fourWide13[21]! =
    expandTree 6 1792 fourRows13[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row22 : fourWide13[22]! =
    expandTree 6 1792 fourRows13[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row23 : fourWide13[23]! =
    expandTree 6 1792 fourRows13[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row24 : fourWide13[24]! =
    expandTree 6 1792 fourRows13[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row25 : fourWide13[25]! =
    expandTree 6 1792 fourRows13[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row26 : fourWide13[26]! =
    expandTree 6 1792 fourRows13[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row27 : fourWide13[27]! =
    expandTree 6 1792 fourRows13[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row28 : fourWide13[28]! =
    expandTree 6 1792 fourRows13[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row29 : fourWide13[29]! =
    expandTree 6 1792 fourRows13[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row30 : fourWide13[30]! =
    expandTree 6 1792 fourRows13[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded13_row31 : fourWide13[31]! =
    expandTree 6 1792 fourRows13[31]! := by decide +kernel

private theorem expanded13 : fourWide13 =
    fourRows13.map (expandTree 6 1792) := by
  change [fourWide13[0]!,
    fourWide13[1]!,
    fourWide13[2]!,
    fourWide13[3]!,
    fourWide13[4]!,
    fourWide13[5]!,
    fourWide13[6]!,
    fourWide13[7]!,
    fourWide13[8]!,
    fourWide13[9]!,
    fourWide13[10]!,
    fourWide13[11]!,
    fourWide13[12]!,
    fourWide13[13]!,
    fourWide13[14]!,
    fourWide13[15]!,
    fourWide13[16]!,
    fourWide13[17]!,
    fourWide13[18]!,
    fourWide13[19]!,
    fourWide13[20]!,
    fourWide13[21]!,
    fourWide13[22]!,
    fourWide13[23]!,
    fourWide13[24]!,
    fourWide13[25]!,
    fourWide13[26]!,
    fourWide13[27]!,
    fourWide13[28]!,
    fourWide13[29]!,
    fourWide13[30]!,
    fourWide13[31]!] =
    [expandTree 6 1792 fourRows13[0]!,
     expandTree 6 1792 fourRows13[1]!,
     expandTree 6 1792 fourRows13[2]!,
     expandTree 6 1792 fourRows13[3]!,
     expandTree 6 1792 fourRows13[4]!,
     expandTree 6 1792 fourRows13[5]!,
     expandTree 6 1792 fourRows13[6]!,
     expandTree 6 1792 fourRows13[7]!,
     expandTree 6 1792 fourRows13[8]!,
     expandTree 6 1792 fourRows13[9]!,
     expandTree 6 1792 fourRows13[10]!,
     expandTree 6 1792 fourRows13[11]!,
     expandTree 6 1792 fourRows13[12]!,
     expandTree 6 1792 fourRows13[13]!,
     expandTree 6 1792 fourRows13[14]!,
     expandTree 6 1792 fourRows13[15]!,
     expandTree 6 1792 fourRows13[16]!,
     expandTree 6 1792 fourRows13[17]!,
     expandTree 6 1792 fourRows13[18]!,
     expandTree 6 1792 fourRows13[19]!,
     expandTree 6 1792 fourRows13[20]!,
     expandTree 6 1792 fourRows13[21]!,
     expandTree 6 1792 fourRows13[22]!,
     expandTree 6 1792 fourRows13[23]!,
     expandTree 6 1792 fourRows13[24]!,
     expandTree 6 1792 fourRows13[25]!,
     expandTree 6 1792 fourRows13[26]!,
     expandTree 6 1792 fourRows13[27]!,
     expandTree 6 1792 fourRows13[28]!,
     expandTree 6 1792 fourRows13[29]!,
     expandTree 6 1792 fourRows13[30]!,
     expandTree 6 1792 fourRows13[31]!]
  rw [expanded13_row00, expanded13_row01, expanded13_row02, expanded13_row03, expanded13_row04, expanded13_row05, expanded13_row06, expanded13_row07, expanded13_row08, expanded13_row09, expanded13_row10, expanded13_row11, expanded13_row12, expanded13_row13, expanded13_row14, expanded13_row15, expanded13_row16, expanded13_row17, expanded13_row18, expanded13_row19, expanded13_row20, expanded13_row21, expanded13_row22, expanded13_row23, expanded13_row24, expanded13_row25, expanded13_row26, expanded13_row27, expanded13_row28, expanded13_row29, expanded13_row30, expanded13_row31]

set_option maxRecDepth 8192 in
private theorem expanded14_row00 : fourWide14[0]! =
    expandTree 6 1792 fourRows14[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row01 : fourWide14[1]! =
    expandTree 6 1792 fourRows14[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row02 : fourWide14[2]! =
    expandTree 6 1792 fourRows14[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row03 : fourWide14[3]! =
    expandTree 6 1792 fourRows14[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row04 : fourWide14[4]! =
    expandTree 6 1792 fourRows14[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row05 : fourWide14[5]! =
    expandTree 6 1792 fourRows14[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row06 : fourWide14[6]! =
    expandTree 6 1792 fourRows14[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row07 : fourWide14[7]! =
    expandTree 6 1792 fourRows14[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row08 : fourWide14[8]! =
    expandTree 6 1792 fourRows14[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row09 : fourWide14[9]! =
    expandTree 6 1792 fourRows14[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row10 : fourWide14[10]! =
    expandTree 6 1792 fourRows14[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row11 : fourWide14[11]! =
    expandTree 6 1792 fourRows14[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row12 : fourWide14[12]! =
    expandTree 6 1792 fourRows14[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row13 : fourWide14[13]! =
    expandTree 6 1792 fourRows14[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row14 : fourWide14[14]! =
    expandTree 6 1792 fourRows14[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row15 : fourWide14[15]! =
    expandTree 6 1792 fourRows14[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row16 : fourWide14[16]! =
    expandTree 6 1792 fourRows14[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row17 : fourWide14[17]! =
    expandTree 6 1792 fourRows14[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row18 : fourWide14[18]! =
    expandTree 6 1792 fourRows14[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row19 : fourWide14[19]! =
    expandTree 6 1792 fourRows14[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row20 : fourWide14[20]! =
    expandTree 6 1792 fourRows14[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row21 : fourWide14[21]! =
    expandTree 6 1792 fourRows14[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row22 : fourWide14[22]! =
    expandTree 6 1792 fourRows14[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row23 : fourWide14[23]! =
    expandTree 6 1792 fourRows14[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row24 : fourWide14[24]! =
    expandTree 6 1792 fourRows14[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row25 : fourWide14[25]! =
    expandTree 6 1792 fourRows14[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row26 : fourWide14[26]! =
    expandTree 6 1792 fourRows14[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row27 : fourWide14[27]! =
    expandTree 6 1792 fourRows14[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row28 : fourWide14[28]! =
    expandTree 6 1792 fourRows14[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row29 : fourWide14[29]! =
    expandTree 6 1792 fourRows14[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row30 : fourWide14[30]! =
    expandTree 6 1792 fourRows14[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded14_row31 : fourWide14[31]! =
    expandTree 6 1792 fourRows14[31]! := by decide +kernel

private theorem expanded14 : fourWide14 =
    fourRows14.map (expandTree 6 1792) := by
  change [fourWide14[0]!,
    fourWide14[1]!,
    fourWide14[2]!,
    fourWide14[3]!,
    fourWide14[4]!,
    fourWide14[5]!,
    fourWide14[6]!,
    fourWide14[7]!,
    fourWide14[8]!,
    fourWide14[9]!,
    fourWide14[10]!,
    fourWide14[11]!,
    fourWide14[12]!,
    fourWide14[13]!,
    fourWide14[14]!,
    fourWide14[15]!,
    fourWide14[16]!,
    fourWide14[17]!,
    fourWide14[18]!,
    fourWide14[19]!,
    fourWide14[20]!,
    fourWide14[21]!,
    fourWide14[22]!,
    fourWide14[23]!,
    fourWide14[24]!,
    fourWide14[25]!,
    fourWide14[26]!,
    fourWide14[27]!,
    fourWide14[28]!,
    fourWide14[29]!,
    fourWide14[30]!,
    fourWide14[31]!] =
    [expandTree 6 1792 fourRows14[0]!,
     expandTree 6 1792 fourRows14[1]!,
     expandTree 6 1792 fourRows14[2]!,
     expandTree 6 1792 fourRows14[3]!,
     expandTree 6 1792 fourRows14[4]!,
     expandTree 6 1792 fourRows14[5]!,
     expandTree 6 1792 fourRows14[6]!,
     expandTree 6 1792 fourRows14[7]!,
     expandTree 6 1792 fourRows14[8]!,
     expandTree 6 1792 fourRows14[9]!,
     expandTree 6 1792 fourRows14[10]!,
     expandTree 6 1792 fourRows14[11]!,
     expandTree 6 1792 fourRows14[12]!,
     expandTree 6 1792 fourRows14[13]!,
     expandTree 6 1792 fourRows14[14]!,
     expandTree 6 1792 fourRows14[15]!,
     expandTree 6 1792 fourRows14[16]!,
     expandTree 6 1792 fourRows14[17]!,
     expandTree 6 1792 fourRows14[18]!,
     expandTree 6 1792 fourRows14[19]!,
     expandTree 6 1792 fourRows14[20]!,
     expandTree 6 1792 fourRows14[21]!,
     expandTree 6 1792 fourRows14[22]!,
     expandTree 6 1792 fourRows14[23]!,
     expandTree 6 1792 fourRows14[24]!,
     expandTree 6 1792 fourRows14[25]!,
     expandTree 6 1792 fourRows14[26]!,
     expandTree 6 1792 fourRows14[27]!,
     expandTree 6 1792 fourRows14[28]!,
     expandTree 6 1792 fourRows14[29]!,
     expandTree 6 1792 fourRows14[30]!,
     expandTree 6 1792 fourRows14[31]!]
  rw [expanded14_row00, expanded14_row01, expanded14_row02, expanded14_row03, expanded14_row04, expanded14_row05, expanded14_row06, expanded14_row07, expanded14_row08, expanded14_row09, expanded14_row10, expanded14_row11, expanded14_row12, expanded14_row13, expanded14_row14, expanded14_row15, expanded14_row16, expanded14_row17, expanded14_row18, expanded14_row19, expanded14_row20, expanded14_row21, expanded14_row22, expanded14_row23, expanded14_row24, expanded14_row25, expanded14_row26, expanded14_row27, expanded14_row28, expanded14_row29, expanded14_row30, expanded14_row31]

set_option maxRecDepth 8192 in
private theorem expanded15_row00 : fourWide15[0]! =
    expandTree 6 1792 fourRows15[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row01 : fourWide15[1]! =
    expandTree 6 1792 fourRows15[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row02 : fourWide15[2]! =
    expandTree 6 1792 fourRows15[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row03 : fourWide15[3]! =
    expandTree 6 1792 fourRows15[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row04 : fourWide15[4]! =
    expandTree 6 1792 fourRows15[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row05 : fourWide15[5]! =
    expandTree 6 1792 fourRows15[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row06 : fourWide15[6]! =
    expandTree 6 1792 fourRows15[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row07 : fourWide15[7]! =
    expandTree 6 1792 fourRows15[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row08 : fourWide15[8]! =
    expandTree 6 1792 fourRows15[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row09 : fourWide15[9]! =
    expandTree 6 1792 fourRows15[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row10 : fourWide15[10]! =
    expandTree 6 1792 fourRows15[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row11 : fourWide15[11]! =
    expandTree 6 1792 fourRows15[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row12 : fourWide15[12]! =
    expandTree 6 1792 fourRows15[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row13 : fourWide15[13]! =
    expandTree 6 1792 fourRows15[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row14 : fourWide15[14]! =
    expandTree 6 1792 fourRows15[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row15 : fourWide15[15]! =
    expandTree 6 1792 fourRows15[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row16 : fourWide15[16]! =
    expandTree 6 1792 fourRows15[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row17 : fourWide15[17]! =
    expandTree 6 1792 fourRows15[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row18 : fourWide15[18]! =
    expandTree 6 1792 fourRows15[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row19 : fourWide15[19]! =
    expandTree 6 1792 fourRows15[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row20 : fourWide15[20]! =
    expandTree 6 1792 fourRows15[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row21 : fourWide15[21]! =
    expandTree 6 1792 fourRows15[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row22 : fourWide15[22]! =
    expandTree 6 1792 fourRows15[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row23 : fourWide15[23]! =
    expandTree 6 1792 fourRows15[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row24 : fourWide15[24]! =
    expandTree 6 1792 fourRows15[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row25 : fourWide15[25]! =
    expandTree 6 1792 fourRows15[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row26 : fourWide15[26]! =
    expandTree 6 1792 fourRows15[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row27 : fourWide15[27]! =
    expandTree 6 1792 fourRows15[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row28 : fourWide15[28]! =
    expandTree 6 1792 fourRows15[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row29 : fourWide15[29]! =
    expandTree 6 1792 fourRows15[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row30 : fourWide15[30]! =
    expandTree 6 1792 fourRows15[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded15_row31 : fourWide15[31]! =
    expandTree 6 1792 fourRows15[31]! := by decide +kernel

private theorem expanded15 : fourWide15 =
    fourRows15.map (expandTree 6 1792) := by
  change [fourWide15[0]!,
    fourWide15[1]!,
    fourWide15[2]!,
    fourWide15[3]!,
    fourWide15[4]!,
    fourWide15[5]!,
    fourWide15[6]!,
    fourWide15[7]!,
    fourWide15[8]!,
    fourWide15[9]!,
    fourWide15[10]!,
    fourWide15[11]!,
    fourWide15[12]!,
    fourWide15[13]!,
    fourWide15[14]!,
    fourWide15[15]!,
    fourWide15[16]!,
    fourWide15[17]!,
    fourWide15[18]!,
    fourWide15[19]!,
    fourWide15[20]!,
    fourWide15[21]!,
    fourWide15[22]!,
    fourWide15[23]!,
    fourWide15[24]!,
    fourWide15[25]!,
    fourWide15[26]!,
    fourWide15[27]!,
    fourWide15[28]!,
    fourWide15[29]!,
    fourWide15[30]!,
    fourWide15[31]!] =
    [expandTree 6 1792 fourRows15[0]!,
     expandTree 6 1792 fourRows15[1]!,
     expandTree 6 1792 fourRows15[2]!,
     expandTree 6 1792 fourRows15[3]!,
     expandTree 6 1792 fourRows15[4]!,
     expandTree 6 1792 fourRows15[5]!,
     expandTree 6 1792 fourRows15[6]!,
     expandTree 6 1792 fourRows15[7]!,
     expandTree 6 1792 fourRows15[8]!,
     expandTree 6 1792 fourRows15[9]!,
     expandTree 6 1792 fourRows15[10]!,
     expandTree 6 1792 fourRows15[11]!,
     expandTree 6 1792 fourRows15[12]!,
     expandTree 6 1792 fourRows15[13]!,
     expandTree 6 1792 fourRows15[14]!,
     expandTree 6 1792 fourRows15[15]!,
     expandTree 6 1792 fourRows15[16]!,
     expandTree 6 1792 fourRows15[17]!,
     expandTree 6 1792 fourRows15[18]!,
     expandTree 6 1792 fourRows15[19]!,
     expandTree 6 1792 fourRows15[20]!,
     expandTree 6 1792 fourRows15[21]!,
     expandTree 6 1792 fourRows15[22]!,
     expandTree 6 1792 fourRows15[23]!,
     expandTree 6 1792 fourRows15[24]!,
     expandTree 6 1792 fourRows15[25]!,
     expandTree 6 1792 fourRows15[26]!,
     expandTree 6 1792 fourRows15[27]!,
     expandTree 6 1792 fourRows15[28]!,
     expandTree 6 1792 fourRows15[29]!,
     expandTree 6 1792 fourRows15[30]!,
     expandTree 6 1792 fourRows15[31]!]
  rw [expanded15_row00, expanded15_row01, expanded15_row02, expanded15_row03, expanded15_row04, expanded15_row05, expanded15_row06, expanded15_row07, expanded15_row08, expanded15_row09, expanded15_row10, expanded15_row11, expanded15_row12, expanded15_row13, expanded15_row14, expanded15_row15, expanded15_row16, expanded15_row17, expanded15_row18, expanded15_row19, expanded15_row20, expanded15_row21, expanded15_row22, expanded15_row23, expanded15_row24, expanded15_row25, expanded15_row26, expanded15_row27, expanded15_row28, expanded15_row29, expanded15_row30, expanded15_row31]

set_option maxRecDepth 8192 in
private theorem expanded16_row00 : fourWide16[0]! =
    expandTree 6 1792 fourRows16[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row01 : fourWide16[1]! =
    expandTree 6 1792 fourRows16[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row02 : fourWide16[2]! =
    expandTree 6 1792 fourRows16[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row03 : fourWide16[3]! =
    expandTree 6 1792 fourRows16[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row04 : fourWide16[4]! =
    expandTree 6 1792 fourRows16[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row05 : fourWide16[5]! =
    expandTree 6 1792 fourRows16[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row06 : fourWide16[6]! =
    expandTree 6 1792 fourRows16[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row07 : fourWide16[7]! =
    expandTree 6 1792 fourRows16[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row08 : fourWide16[8]! =
    expandTree 6 1792 fourRows16[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row09 : fourWide16[9]! =
    expandTree 6 1792 fourRows16[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row10 : fourWide16[10]! =
    expandTree 6 1792 fourRows16[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row11 : fourWide16[11]! =
    expandTree 6 1792 fourRows16[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row12 : fourWide16[12]! =
    expandTree 6 1792 fourRows16[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row13 : fourWide16[13]! =
    expandTree 6 1792 fourRows16[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row14 : fourWide16[14]! =
    expandTree 6 1792 fourRows16[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row15 : fourWide16[15]! =
    expandTree 6 1792 fourRows16[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row16 : fourWide16[16]! =
    expandTree 6 1792 fourRows16[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row17 : fourWide16[17]! =
    expandTree 6 1792 fourRows16[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row18 : fourWide16[18]! =
    expandTree 6 1792 fourRows16[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row19 : fourWide16[19]! =
    expandTree 6 1792 fourRows16[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row20 : fourWide16[20]! =
    expandTree 6 1792 fourRows16[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row21 : fourWide16[21]! =
    expandTree 6 1792 fourRows16[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row22 : fourWide16[22]! =
    expandTree 6 1792 fourRows16[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row23 : fourWide16[23]! =
    expandTree 6 1792 fourRows16[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row24 : fourWide16[24]! =
    expandTree 6 1792 fourRows16[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row25 : fourWide16[25]! =
    expandTree 6 1792 fourRows16[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row26 : fourWide16[26]! =
    expandTree 6 1792 fourRows16[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row27 : fourWide16[27]! =
    expandTree 6 1792 fourRows16[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row28 : fourWide16[28]! =
    expandTree 6 1792 fourRows16[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row29 : fourWide16[29]! =
    expandTree 6 1792 fourRows16[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row30 : fourWide16[30]! =
    expandTree 6 1792 fourRows16[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded16_row31 : fourWide16[31]! =
    expandTree 6 1792 fourRows16[31]! := by decide +kernel

private theorem expanded16 : fourWide16 =
    fourRows16.map (expandTree 6 1792) := by
  change [fourWide16[0]!,
    fourWide16[1]!,
    fourWide16[2]!,
    fourWide16[3]!,
    fourWide16[4]!,
    fourWide16[5]!,
    fourWide16[6]!,
    fourWide16[7]!,
    fourWide16[8]!,
    fourWide16[9]!,
    fourWide16[10]!,
    fourWide16[11]!,
    fourWide16[12]!,
    fourWide16[13]!,
    fourWide16[14]!,
    fourWide16[15]!,
    fourWide16[16]!,
    fourWide16[17]!,
    fourWide16[18]!,
    fourWide16[19]!,
    fourWide16[20]!,
    fourWide16[21]!,
    fourWide16[22]!,
    fourWide16[23]!,
    fourWide16[24]!,
    fourWide16[25]!,
    fourWide16[26]!,
    fourWide16[27]!,
    fourWide16[28]!,
    fourWide16[29]!,
    fourWide16[30]!,
    fourWide16[31]!] =
    [expandTree 6 1792 fourRows16[0]!,
     expandTree 6 1792 fourRows16[1]!,
     expandTree 6 1792 fourRows16[2]!,
     expandTree 6 1792 fourRows16[3]!,
     expandTree 6 1792 fourRows16[4]!,
     expandTree 6 1792 fourRows16[5]!,
     expandTree 6 1792 fourRows16[6]!,
     expandTree 6 1792 fourRows16[7]!,
     expandTree 6 1792 fourRows16[8]!,
     expandTree 6 1792 fourRows16[9]!,
     expandTree 6 1792 fourRows16[10]!,
     expandTree 6 1792 fourRows16[11]!,
     expandTree 6 1792 fourRows16[12]!,
     expandTree 6 1792 fourRows16[13]!,
     expandTree 6 1792 fourRows16[14]!,
     expandTree 6 1792 fourRows16[15]!,
     expandTree 6 1792 fourRows16[16]!,
     expandTree 6 1792 fourRows16[17]!,
     expandTree 6 1792 fourRows16[18]!,
     expandTree 6 1792 fourRows16[19]!,
     expandTree 6 1792 fourRows16[20]!,
     expandTree 6 1792 fourRows16[21]!,
     expandTree 6 1792 fourRows16[22]!,
     expandTree 6 1792 fourRows16[23]!,
     expandTree 6 1792 fourRows16[24]!,
     expandTree 6 1792 fourRows16[25]!,
     expandTree 6 1792 fourRows16[26]!,
     expandTree 6 1792 fourRows16[27]!,
     expandTree 6 1792 fourRows16[28]!,
     expandTree 6 1792 fourRows16[29]!,
     expandTree 6 1792 fourRows16[30]!,
     expandTree 6 1792 fourRows16[31]!]
  rw [expanded16_row00, expanded16_row01, expanded16_row02, expanded16_row03, expanded16_row04, expanded16_row05, expanded16_row06, expanded16_row07, expanded16_row08, expanded16_row09, expanded16_row10, expanded16_row11, expanded16_row12, expanded16_row13, expanded16_row14, expanded16_row15, expanded16_row16, expanded16_row17, expanded16_row18, expanded16_row19, expanded16_row20, expanded16_row21, expanded16_row22, expanded16_row23, expanded16_row24, expanded16_row25, expanded16_row26, expanded16_row27, expanded16_row28, expanded16_row29, expanded16_row30, expanded16_row31]

set_option maxRecDepth 8192 in
private theorem expanded17_row00 : fourWide17[0]! =
    expandTree 6 1792 fourRows17[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row01 : fourWide17[1]! =
    expandTree 6 1792 fourRows17[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row02 : fourWide17[2]! =
    expandTree 6 1792 fourRows17[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row03 : fourWide17[3]! =
    expandTree 6 1792 fourRows17[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row04 : fourWide17[4]! =
    expandTree 6 1792 fourRows17[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row05 : fourWide17[5]! =
    expandTree 6 1792 fourRows17[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row06 : fourWide17[6]! =
    expandTree 6 1792 fourRows17[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row07 : fourWide17[7]! =
    expandTree 6 1792 fourRows17[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row08 : fourWide17[8]! =
    expandTree 6 1792 fourRows17[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row09 : fourWide17[9]! =
    expandTree 6 1792 fourRows17[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row10 : fourWide17[10]! =
    expandTree 6 1792 fourRows17[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row11 : fourWide17[11]! =
    expandTree 6 1792 fourRows17[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row12 : fourWide17[12]! =
    expandTree 6 1792 fourRows17[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row13 : fourWide17[13]! =
    expandTree 6 1792 fourRows17[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row14 : fourWide17[14]! =
    expandTree 6 1792 fourRows17[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row15 : fourWide17[15]! =
    expandTree 6 1792 fourRows17[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row16 : fourWide17[16]! =
    expandTree 6 1792 fourRows17[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row17 : fourWide17[17]! =
    expandTree 6 1792 fourRows17[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row18 : fourWide17[18]! =
    expandTree 6 1792 fourRows17[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row19 : fourWide17[19]! =
    expandTree 6 1792 fourRows17[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row20 : fourWide17[20]! =
    expandTree 6 1792 fourRows17[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row21 : fourWide17[21]! =
    expandTree 6 1792 fourRows17[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row22 : fourWide17[22]! =
    expandTree 6 1792 fourRows17[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row23 : fourWide17[23]! =
    expandTree 6 1792 fourRows17[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row24 : fourWide17[24]! =
    expandTree 6 1792 fourRows17[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row25 : fourWide17[25]! =
    expandTree 6 1792 fourRows17[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row26 : fourWide17[26]! =
    expandTree 6 1792 fourRows17[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row27 : fourWide17[27]! =
    expandTree 6 1792 fourRows17[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row28 : fourWide17[28]! =
    expandTree 6 1792 fourRows17[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row29 : fourWide17[29]! =
    expandTree 6 1792 fourRows17[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row30 : fourWide17[30]! =
    expandTree 6 1792 fourRows17[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded17_row31 : fourWide17[31]! =
    expandTree 6 1792 fourRows17[31]! := by decide +kernel

private theorem expanded17 : fourWide17 =
    fourRows17.map (expandTree 6 1792) := by
  change [fourWide17[0]!,
    fourWide17[1]!,
    fourWide17[2]!,
    fourWide17[3]!,
    fourWide17[4]!,
    fourWide17[5]!,
    fourWide17[6]!,
    fourWide17[7]!,
    fourWide17[8]!,
    fourWide17[9]!,
    fourWide17[10]!,
    fourWide17[11]!,
    fourWide17[12]!,
    fourWide17[13]!,
    fourWide17[14]!,
    fourWide17[15]!,
    fourWide17[16]!,
    fourWide17[17]!,
    fourWide17[18]!,
    fourWide17[19]!,
    fourWide17[20]!,
    fourWide17[21]!,
    fourWide17[22]!,
    fourWide17[23]!,
    fourWide17[24]!,
    fourWide17[25]!,
    fourWide17[26]!,
    fourWide17[27]!,
    fourWide17[28]!,
    fourWide17[29]!,
    fourWide17[30]!,
    fourWide17[31]!] =
    [expandTree 6 1792 fourRows17[0]!,
     expandTree 6 1792 fourRows17[1]!,
     expandTree 6 1792 fourRows17[2]!,
     expandTree 6 1792 fourRows17[3]!,
     expandTree 6 1792 fourRows17[4]!,
     expandTree 6 1792 fourRows17[5]!,
     expandTree 6 1792 fourRows17[6]!,
     expandTree 6 1792 fourRows17[7]!,
     expandTree 6 1792 fourRows17[8]!,
     expandTree 6 1792 fourRows17[9]!,
     expandTree 6 1792 fourRows17[10]!,
     expandTree 6 1792 fourRows17[11]!,
     expandTree 6 1792 fourRows17[12]!,
     expandTree 6 1792 fourRows17[13]!,
     expandTree 6 1792 fourRows17[14]!,
     expandTree 6 1792 fourRows17[15]!,
     expandTree 6 1792 fourRows17[16]!,
     expandTree 6 1792 fourRows17[17]!,
     expandTree 6 1792 fourRows17[18]!,
     expandTree 6 1792 fourRows17[19]!,
     expandTree 6 1792 fourRows17[20]!,
     expandTree 6 1792 fourRows17[21]!,
     expandTree 6 1792 fourRows17[22]!,
     expandTree 6 1792 fourRows17[23]!,
     expandTree 6 1792 fourRows17[24]!,
     expandTree 6 1792 fourRows17[25]!,
     expandTree 6 1792 fourRows17[26]!,
     expandTree 6 1792 fourRows17[27]!,
     expandTree 6 1792 fourRows17[28]!,
     expandTree 6 1792 fourRows17[29]!,
     expandTree 6 1792 fourRows17[30]!,
     expandTree 6 1792 fourRows17[31]!]
  rw [expanded17_row00, expanded17_row01, expanded17_row02, expanded17_row03, expanded17_row04, expanded17_row05, expanded17_row06, expanded17_row07, expanded17_row08, expanded17_row09, expanded17_row10, expanded17_row11, expanded17_row12, expanded17_row13, expanded17_row14, expanded17_row15, expanded17_row16, expanded17_row17, expanded17_row18, expanded17_row19, expanded17_row20, expanded17_row21, expanded17_row22, expanded17_row23, expanded17_row24, expanded17_row25, expanded17_row26, expanded17_row27, expanded17_row28, expanded17_row29, expanded17_row30, expanded17_row31]

set_option maxRecDepth 8192 in
private theorem expanded18_row00 : fourWide18[0]! =
    expandTree 6 1792 fourRows18[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row01 : fourWide18[1]! =
    expandTree 6 1792 fourRows18[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row02 : fourWide18[2]! =
    expandTree 6 1792 fourRows18[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row03 : fourWide18[3]! =
    expandTree 6 1792 fourRows18[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row04 : fourWide18[4]! =
    expandTree 6 1792 fourRows18[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row05 : fourWide18[5]! =
    expandTree 6 1792 fourRows18[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row06 : fourWide18[6]! =
    expandTree 6 1792 fourRows18[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row07 : fourWide18[7]! =
    expandTree 6 1792 fourRows18[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row08 : fourWide18[8]! =
    expandTree 6 1792 fourRows18[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row09 : fourWide18[9]! =
    expandTree 6 1792 fourRows18[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row10 : fourWide18[10]! =
    expandTree 6 1792 fourRows18[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row11 : fourWide18[11]! =
    expandTree 6 1792 fourRows18[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row12 : fourWide18[12]! =
    expandTree 6 1792 fourRows18[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row13 : fourWide18[13]! =
    expandTree 6 1792 fourRows18[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row14 : fourWide18[14]! =
    expandTree 6 1792 fourRows18[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row15 : fourWide18[15]! =
    expandTree 6 1792 fourRows18[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row16 : fourWide18[16]! =
    expandTree 6 1792 fourRows18[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row17 : fourWide18[17]! =
    expandTree 6 1792 fourRows18[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row18 : fourWide18[18]! =
    expandTree 6 1792 fourRows18[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row19 : fourWide18[19]! =
    expandTree 6 1792 fourRows18[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row20 : fourWide18[20]! =
    expandTree 6 1792 fourRows18[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row21 : fourWide18[21]! =
    expandTree 6 1792 fourRows18[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row22 : fourWide18[22]! =
    expandTree 6 1792 fourRows18[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row23 : fourWide18[23]! =
    expandTree 6 1792 fourRows18[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row24 : fourWide18[24]! =
    expandTree 6 1792 fourRows18[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row25 : fourWide18[25]! =
    expandTree 6 1792 fourRows18[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row26 : fourWide18[26]! =
    expandTree 6 1792 fourRows18[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row27 : fourWide18[27]! =
    expandTree 6 1792 fourRows18[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row28 : fourWide18[28]! =
    expandTree 6 1792 fourRows18[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row29 : fourWide18[29]! =
    expandTree 6 1792 fourRows18[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row30 : fourWide18[30]! =
    expandTree 6 1792 fourRows18[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded18_row31 : fourWide18[31]! =
    expandTree 6 1792 fourRows18[31]! := by decide +kernel

private theorem expanded18 : fourWide18 =
    fourRows18.map (expandTree 6 1792) := by
  change [fourWide18[0]!,
    fourWide18[1]!,
    fourWide18[2]!,
    fourWide18[3]!,
    fourWide18[4]!,
    fourWide18[5]!,
    fourWide18[6]!,
    fourWide18[7]!,
    fourWide18[8]!,
    fourWide18[9]!,
    fourWide18[10]!,
    fourWide18[11]!,
    fourWide18[12]!,
    fourWide18[13]!,
    fourWide18[14]!,
    fourWide18[15]!,
    fourWide18[16]!,
    fourWide18[17]!,
    fourWide18[18]!,
    fourWide18[19]!,
    fourWide18[20]!,
    fourWide18[21]!,
    fourWide18[22]!,
    fourWide18[23]!,
    fourWide18[24]!,
    fourWide18[25]!,
    fourWide18[26]!,
    fourWide18[27]!,
    fourWide18[28]!,
    fourWide18[29]!,
    fourWide18[30]!,
    fourWide18[31]!] =
    [expandTree 6 1792 fourRows18[0]!,
     expandTree 6 1792 fourRows18[1]!,
     expandTree 6 1792 fourRows18[2]!,
     expandTree 6 1792 fourRows18[3]!,
     expandTree 6 1792 fourRows18[4]!,
     expandTree 6 1792 fourRows18[5]!,
     expandTree 6 1792 fourRows18[6]!,
     expandTree 6 1792 fourRows18[7]!,
     expandTree 6 1792 fourRows18[8]!,
     expandTree 6 1792 fourRows18[9]!,
     expandTree 6 1792 fourRows18[10]!,
     expandTree 6 1792 fourRows18[11]!,
     expandTree 6 1792 fourRows18[12]!,
     expandTree 6 1792 fourRows18[13]!,
     expandTree 6 1792 fourRows18[14]!,
     expandTree 6 1792 fourRows18[15]!,
     expandTree 6 1792 fourRows18[16]!,
     expandTree 6 1792 fourRows18[17]!,
     expandTree 6 1792 fourRows18[18]!,
     expandTree 6 1792 fourRows18[19]!,
     expandTree 6 1792 fourRows18[20]!,
     expandTree 6 1792 fourRows18[21]!,
     expandTree 6 1792 fourRows18[22]!,
     expandTree 6 1792 fourRows18[23]!,
     expandTree 6 1792 fourRows18[24]!,
     expandTree 6 1792 fourRows18[25]!,
     expandTree 6 1792 fourRows18[26]!,
     expandTree 6 1792 fourRows18[27]!,
     expandTree 6 1792 fourRows18[28]!,
     expandTree 6 1792 fourRows18[29]!,
     expandTree 6 1792 fourRows18[30]!,
     expandTree 6 1792 fourRows18[31]!]
  rw [expanded18_row00, expanded18_row01, expanded18_row02, expanded18_row03, expanded18_row04, expanded18_row05, expanded18_row06, expanded18_row07, expanded18_row08, expanded18_row09, expanded18_row10, expanded18_row11, expanded18_row12, expanded18_row13, expanded18_row14, expanded18_row15, expanded18_row16, expanded18_row17, expanded18_row18, expanded18_row19, expanded18_row20, expanded18_row21, expanded18_row22, expanded18_row23, expanded18_row24, expanded18_row25, expanded18_row26, expanded18_row27, expanded18_row28, expanded18_row29, expanded18_row30, expanded18_row31]

set_option maxRecDepth 8192 in
private theorem expanded19_row00 : fourWide19[0]! =
    expandTree 6 1792 fourRows19[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row01 : fourWide19[1]! =
    expandTree 6 1792 fourRows19[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row02 : fourWide19[2]! =
    expandTree 6 1792 fourRows19[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row03 : fourWide19[3]! =
    expandTree 6 1792 fourRows19[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row04 : fourWide19[4]! =
    expandTree 6 1792 fourRows19[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row05 : fourWide19[5]! =
    expandTree 6 1792 fourRows19[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row06 : fourWide19[6]! =
    expandTree 6 1792 fourRows19[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row07 : fourWide19[7]! =
    expandTree 6 1792 fourRows19[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row08 : fourWide19[8]! =
    expandTree 6 1792 fourRows19[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row09 : fourWide19[9]! =
    expandTree 6 1792 fourRows19[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row10 : fourWide19[10]! =
    expandTree 6 1792 fourRows19[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row11 : fourWide19[11]! =
    expandTree 6 1792 fourRows19[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row12 : fourWide19[12]! =
    expandTree 6 1792 fourRows19[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row13 : fourWide19[13]! =
    expandTree 6 1792 fourRows19[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row14 : fourWide19[14]! =
    expandTree 6 1792 fourRows19[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row15 : fourWide19[15]! =
    expandTree 6 1792 fourRows19[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row16 : fourWide19[16]! =
    expandTree 6 1792 fourRows19[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row17 : fourWide19[17]! =
    expandTree 6 1792 fourRows19[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row18 : fourWide19[18]! =
    expandTree 6 1792 fourRows19[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row19 : fourWide19[19]! =
    expandTree 6 1792 fourRows19[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row20 : fourWide19[20]! =
    expandTree 6 1792 fourRows19[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row21 : fourWide19[21]! =
    expandTree 6 1792 fourRows19[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row22 : fourWide19[22]! =
    expandTree 6 1792 fourRows19[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row23 : fourWide19[23]! =
    expandTree 6 1792 fourRows19[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row24 : fourWide19[24]! =
    expandTree 6 1792 fourRows19[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row25 : fourWide19[25]! =
    expandTree 6 1792 fourRows19[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row26 : fourWide19[26]! =
    expandTree 6 1792 fourRows19[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row27 : fourWide19[27]! =
    expandTree 6 1792 fourRows19[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row28 : fourWide19[28]! =
    expandTree 6 1792 fourRows19[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row29 : fourWide19[29]! =
    expandTree 6 1792 fourRows19[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row30 : fourWide19[30]! =
    expandTree 6 1792 fourRows19[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded19_row31 : fourWide19[31]! =
    expandTree 6 1792 fourRows19[31]! := by decide +kernel

private theorem expanded19 : fourWide19 =
    fourRows19.map (expandTree 6 1792) := by
  change [fourWide19[0]!,
    fourWide19[1]!,
    fourWide19[2]!,
    fourWide19[3]!,
    fourWide19[4]!,
    fourWide19[5]!,
    fourWide19[6]!,
    fourWide19[7]!,
    fourWide19[8]!,
    fourWide19[9]!,
    fourWide19[10]!,
    fourWide19[11]!,
    fourWide19[12]!,
    fourWide19[13]!,
    fourWide19[14]!,
    fourWide19[15]!,
    fourWide19[16]!,
    fourWide19[17]!,
    fourWide19[18]!,
    fourWide19[19]!,
    fourWide19[20]!,
    fourWide19[21]!,
    fourWide19[22]!,
    fourWide19[23]!,
    fourWide19[24]!,
    fourWide19[25]!,
    fourWide19[26]!,
    fourWide19[27]!,
    fourWide19[28]!,
    fourWide19[29]!,
    fourWide19[30]!,
    fourWide19[31]!] =
    [expandTree 6 1792 fourRows19[0]!,
     expandTree 6 1792 fourRows19[1]!,
     expandTree 6 1792 fourRows19[2]!,
     expandTree 6 1792 fourRows19[3]!,
     expandTree 6 1792 fourRows19[4]!,
     expandTree 6 1792 fourRows19[5]!,
     expandTree 6 1792 fourRows19[6]!,
     expandTree 6 1792 fourRows19[7]!,
     expandTree 6 1792 fourRows19[8]!,
     expandTree 6 1792 fourRows19[9]!,
     expandTree 6 1792 fourRows19[10]!,
     expandTree 6 1792 fourRows19[11]!,
     expandTree 6 1792 fourRows19[12]!,
     expandTree 6 1792 fourRows19[13]!,
     expandTree 6 1792 fourRows19[14]!,
     expandTree 6 1792 fourRows19[15]!,
     expandTree 6 1792 fourRows19[16]!,
     expandTree 6 1792 fourRows19[17]!,
     expandTree 6 1792 fourRows19[18]!,
     expandTree 6 1792 fourRows19[19]!,
     expandTree 6 1792 fourRows19[20]!,
     expandTree 6 1792 fourRows19[21]!,
     expandTree 6 1792 fourRows19[22]!,
     expandTree 6 1792 fourRows19[23]!,
     expandTree 6 1792 fourRows19[24]!,
     expandTree 6 1792 fourRows19[25]!,
     expandTree 6 1792 fourRows19[26]!,
     expandTree 6 1792 fourRows19[27]!,
     expandTree 6 1792 fourRows19[28]!,
     expandTree 6 1792 fourRows19[29]!,
     expandTree 6 1792 fourRows19[30]!,
     expandTree 6 1792 fourRows19[31]!]
  rw [expanded19_row00, expanded19_row01, expanded19_row02, expanded19_row03, expanded19_row04, expanded19_row05, expanded19_row06, expanded19_row07, expanded19_row08, expanded19_row09, expanded19_row10, expanded19_row11, expanded19_row12, expanded19_row13, expanded19_row14, expanded19_row15, expanded19_row16, expanded19_row17, expanded19_row18, expanded19_row19, expanded19_row20, expanded19_row21, expanded19_row22, expanded19_row23, expanded19_row24, expanded19_row25, expanded19_row26, expanded19_row27, expanded19_row28, expanded19_row29, expanded19_row30, expanded19_row31]

set_option maxRecDepth 8192 in
private theorem expanded20_row00 : fourWide20[0]! =
    expandTree 6 1792 fourRows20[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row01 : fourWide20[1]! =
    expandTree 6 1792 fourRows20[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row02 : fourWide20[2]! =
    expandTree 6 1792 fourRows20[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row03 : fourWide20[3]! =
    expandTree 6 1792 fourRows20[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row04 : fourWide20[4]! =
    expandTree 6 1792 fourRows20[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row05 : fourWide20[5]! =
    expandTree 6 1792 fourRows20[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row06 : fourWide20[6]! =
    expandTree 6 1792 fourRows20[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row07 : fourWide20[7]! =
    expandTree 6 1792 fourRows20[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row08 : fourWide20[8]! =
    expandTree 6 1792 fourRows20[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row09 : fourWide20[9]! =
    expandTree 6 1792 fourRows20[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row10 : fourWide20[10]! =
    expandTree 6 1792 fourRows20[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row11 : fourWide20[11]! =
    expandTree 6 1792 fourRows20[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row12 : fourWide20[12]! =
    expandTree 6 1792 fourRows20[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row13 : fourWide20[13]! =
    expandTree 6 1792 fourRows20[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row14 : fourWide20[14]! =
    expandTree 6 1792 fourRows20[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row15 : fourWide20[15]! =
    expandTree 6 1792 fourRows20[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row16 : fourWide20[16]! =
    expandTree 6 1792 fourRows20[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row17 : fourWide20[17]! =
    expandTree 6 1792 fourRows20[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row18 : fourWide20[18]! =
    expandTree 6 1792 fourRows20[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row19 : fourWide20[19]! =
    expandTree 6 1792 fourRows20[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row20 : fourWide20[20]! =
    expandTree 6 1792 fourRows20[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row21 : fourWide20[21]! =
    expandTree 6 1792 fourRows20[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row22 : fourWide20[22]! =
    expandTree 6 1792 fourRows20[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row23 : fourWide20[23]! =
    expandTree 6 1792 fourRows20[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row24 : fourWide20[24]! =
    expandTree 6 1792 fourRows20[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row25 : fourWide20[25]! =
    expandTree 6 1792 fourRows20[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row26 : fourWide20[26]! =
    expandTree 6 1792 fourRows20[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row27 : fourWide20[27]! =
    expandTree 6 1792 fourRows20[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row28 : fourWide20[28]! =
    expandTree 6 1792 fourRows20[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row29 : fourWide20[29]! =
    expandTree 6 1792 fourRows20[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row30 : fourWide20[30]! =
    expandTree 6 1792 fourRows20[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded20_row31 : fourWide20[31]! =
    expandTree 6 1792 fourRows20[31]! := by decide +kernel

private theorem expanded20 : fourWide20 =
    fourRows20.map (expandTree 6 1792) := by
  change [fourWide20[0]!,
    fourWide20[1]!,
    fourWide20[2]!,
    fourWide20[3]!,
    fourWide20[4]!,
    fourWide20[5]!,
    fourWide20[6]!,
    fourWide20[7]!,
    fourWide20[8]!,
    fourWide20[9]!,
    fourWide20[10]!,
    fourWide20[11]!,
    fourWide20[12]!,
    fourWide20[13]!,
    fourWide20[14]!,
    fourWide20[15]!,
    fourWide20[16]!,
    fourWide20[17]!,
    fourWide20[18]!,
    fourWide20[19]!,
    fourWide20[20]!,
    fourWide20[21]!,
    fourWide20[22]!,
    fourWide20[23]!,
    fourWide20[24]!,
    fourWide20[25]!,
    fourWide20[26]!,
    fourWide20[27]!,
    fourWide20[28]!,
    fourWide20[29]!,
    fourWide20[30]!,
    fourWide20[31]!] =
    [expandTree 6 1792 fourRows20[0]!,
     expandTree 6 1792 fourRows20[1]!,
     expandTree 6 1792 fourRows20[2]!,
     expandTree 6 1792 fourRows20[3]!,
     expandTree 6 1792 fourRows20[4]!,
     expandTree 6 1792 fourRows20[5]!,
     expandTree 6 1792 fourRows20[6]!,
     expandTree 6 1792 fourRows20[7]!,
     expandTree 6 1792 fourRows20[8]!,
     expandTree 6 1792 fourRows20[9]!,
     expandTree 6 1792 fourRows20[10]!,
     expandTree 6 1792 fourRows20[11]!,
     expandTree 6 1792 fourRows20[12]!,
     expandTree 6 1792 fourRows20[13]!,
     expandTree 6 1792 fourRows20[14]!,
     expandTree 6 1792 fourRows20[15]!,
     expandTree 6 1792 fourRows20[16]!,
     expandTree 6 1792 fourRows20[17]!,
     expandTree 6 1792 fourRows20[18]!,
     expandTree 6 1792 fourRows20[19]!,
     expandTree 6 1792 fourRows20[20]!,
     expandTree 6 1792 fourRows20[21]!,
     expandTree 6 1792 fourRows20[22]!,
     expandTree 6 1792 fourRows20[23]!,
     expandTree 6 1792 fourRows20[24]!,
     expandTree 6 1792 fourRows20[25]!,
     expandTree 6 1792 fourRows20[26]!,
     expandTree 6 1792 fourRows20[27]!,
     expandTree 6 1792 fourRows20[28]!,
     expandTree 6 1792 fourRows20[29]!,
     expandTree 6 1792 fourRows20[30]!,
     expandTree 6 1792 fourRows20[31]!]
  rw [expanded20_row00, expanded20_row01, expanded20_row02, expanded20_row03, expanded20_row04, expanded20_row05, expanded20_row06, expanded20_row07, expanded20_row08, expanded20_row09, expanded20_row10, expanded20_row11, expanded20_row12, expanded20_row13, expanded20_row14, expanded20_row15, expanded20_row16, expanded20_row17, expanded20_row18, expanded20_row19, expanded20_row20, expanded20_row21, expanded20_row22, expanded20_row23, expanded20_row24, expanded20_row25, expanded20_row26, expanded20_row27, expanded20_row28, expanded20_row29, expanded20_row30, expanded20_row31]

set_option maxRecDepth 8192 in
private theorem expanded21_row00 : fourWide21[0]! =
    expandTree 6 1792 fourRows21[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row01 : fourWide21[1]! =
    expandTree 6 1792 fourRows21[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row02 : fourWide21[2]! =
    expandTree 6 1792 fourRows21[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row03 : fourWide21[3]! =
    expandTree 6 1792 fourRows21[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row04 : fourWide21[4]! =
    expandTree 6 1792 fourRows21[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row05 : fourWide21[5]! =
    expandTree 6 1792 fourRows21[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row06 : fourWide21[6]! =
    expandTree 6 1792 fourRows21[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row07 : fourWide21[7]! =
    expandTree 6 1792 fourRows21[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row08 : fourWide21[8]! =
    expandTree 6 1792 fourRows21[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row09 : fourWide21[9]! =
    expandTree 6 1792 fourRows21[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row10 : fourWide21[10]! =
    expandTree 6 1792 fourRows21[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row11 : fourWide21[11]! =
    expandTree 6 1792 fourRows21[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row12 : fourWide21[12]! =
    expandTree 6 1792 fourRows21[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row13 : fourWide21[13]! =
    expandTree 6 1792 fourRows21[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row14 : fourWide21[14]! =
    expandTree 6 1792 fourRows21[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row15 : fourWide21[15]! =
    expandTree 6 1792 fourRows21[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row16 : fourWide21[16]! =
    expandTree 6 1792 fourRows21[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row17 : fourWide21[17]! =
    expandTree 6 1792 fourRows21[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row18 : fourWide21[18]! =
    expandTree 6 1792 fourRows21[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row19 : fourWide21[19]! =
    expandTree 6 1792 fourRows21[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row20 : fourWide21[20]! =
    expandTree 6 1792 fourRows21[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row21 : fourWide21[21]! =
    expandTree 6 1792 fourRows21[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row22 : fourWide21[22]! =
    expandTree 6 1792 fourRows21[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row23 : fourWide21[23]! =
    expandTree 6 1792 fourRows21[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row24 : fourWide21[24]! =
    expandTree 6 1792 fourRows21[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row25 : fourWide21[25]! =
    expandTree 6 1792 fourRows21[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row26 : fourWide21[26]! =
    expandTree 6 1792 fourRows21[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row27 : fourWide21[27]! =
    expandTree 6 1792 fourRows21[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row28 : fourWide21[28]! =
    expandTree 6 1792 fourRows21[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row29 : fourWide21[29]! =
    expandTree 6 1792 fourRows21[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row30 : fourWide21[30]! =
    expandTree 6 1792 fourRows21[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded21_row31 : fourWide21[31]! =
    expandTree 6 1792 fourRows21[31]! := by decide +kernel

private theorem expanded21 : fourWide21 =
    fourRows21.map (expandTree 6 1792) := by
  change [fourWide21[0]!,
    fourWide21[1]!,
    fourWide21[2]!,
    fourWide21[3]!,
    fourWide21[4]!,
    fourWide21[5]!,
    fourWide21[6]!,
    fourWide21[7]!,
    fourWide21[8]!,
    fourWide21[9]!,
    fourWide21[10]!,
    fourWide21[11]!,
    fourWide21[12]!,
    fourWide21[13]!,
    fourWide21[14]!,
    fourWide21[15]!,
    fourWide21[16]!,
    fourWide21[17]!,
    fourWide21[18]!,
    fourWide21[19]!,
    fourWide21[20]!,
    fourWide21[21]!,
    fourWide21[22]!,
    fourWide21[23]!,
    fourWide21[24]!,
    fourWide21[25]!,
    fourWide21[26]!,
    fourWide21[27]!,
    fourWide21[28]!,
    fourWide21[29]!,
    fourWide21[30]!,
    fourWide21[31]!] =
    [expandTree 6 1792 fourRows21[0]!,
     expandTree 6 1792 fourRows21[1]!,
     expandTree 6 1792 fourRows21[2]!,
     expandTree 6 1792 fourRows21[3]!,
     expandTree 6 1792 fourRows21[4]!,
     expandTree 6 1792 fourRows21[5]!,
     expandTree 6 1792 fourRows21[6]!,
     expandTree 6 1792 fourRows21[7]!,
     expandTree 6 1792 fourRows21[8]!,
     expandTree 6 1792 fourRows21[9]!,
     expandTree 6 1792 fourRows21[10]!,
     expandTree 6 1792 fourRows21[11]!,
     expandTree 6 1792 fourRows21[12]!,
     expandTree 6 1792 fourRows21[13]!,
     expandTree 6 1792 fourRows21[14]!,
     expandTree 6 1792 fourRows21[15]!,
     expandTree 6 1792 fourRows21[16]!,
     expandTree 6 1792 fourRows21[17]!,
     expandTree 6 1792 fourRows21[18]!,
     expandTree 6 1792 fourRows21[19]!,
     expandTree 6 1792 fourRows21[20]!,
     expandTree 6 1792 fourRows21[21]!,
     expandTree 6 1792 fourRows21[22]!,
     expandTree 6 1792 fourRows21[23]!,
     expandTree 6 1792 fourRows21[24]!,
     expandTree 6 1792 fourRows21[25]!,
     expandTree 6 1792 fourRows21[26]!,
     expandTree 6 1792 fourRows21[27]!,
     expandTree 6 1792 fourRows21[28]!,
     expandTree 6 1792 fourRows21[29]!,
     expandTree 6 1792 fourRows21[30]!,
     expandTree 6 1792 fourRows21[31]!]
  rw [expanded21_row00, expanded21_row01, expanded21_row02, expanded21_row03, expanded21_row04, expanded21_row05, expanded21_row06, expanded21_row07, expanded21_row08, expanded21_row09, expanded21_row10, expanded21_row11, expanded21_row12, expanded21_row13, expanded21_row14, expanded21_row15, expanded21_row16, expanded21_row17, expanded21_row18, expanded21_row19, expanded21_row20, expanded21_row21, expanded21_row22, expanded21_row23, expanded21_row24, expanded21_row25, expanded21_row26, expanded21_row27, expanded21_row28, expanded21_row29, expanded21_row30, expanded21_row31]

set_option maxRecDepth 8192 in
private theorem expanded22_row00 : fourWide22[0]! =
    expandTree 6 1792 fourRows22[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row01 : fourWide22[1]! =
    expandTree 6 1792 fourRows22[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row02 : fourWide22[2]! =
    expandTree 6 1792 fourRows22[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row03 : fourWide22[3]! =
    expandTree 6 1792 fourRows22[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row04 : fourWide22[4]! =
    expandTree 6 1792 fourRows22[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row05 : fourWide22[5]! =
    expandTree 6 1792 fourRows22[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row06 : fourWide22[6]! =
    expandTree 6 1792 fourRows22[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row07 : fourWide22[7]! =
    expandTree 6 1792 fourRows22[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row08 : fourWide22[8]! =
    expandTree 6 1792 fourRows22[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row09 : fourWide22[9]! =
    expandTree 6 1792 fourRows22[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row10 : fourWide22[10]! =
    expandTree 6 1792 fourRows22[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row11 : fourWide22[11]! =
    expandTree 6 1792 fourRows22[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row12 : fourWide22[12]! =
    expandTree 6 1792 fourRows22[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row13 : fourWide22[13]! =
    expandTree 6 1792 fourRows22[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row14 : fourWide22[14]! =
    expandTree 6 1792 fourRows22[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row15 : fourWide22[15]! =
    expandTree 6 1792 fourRows22[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row16 : fourWide22[16]! =
    expandTree 6 1792 fourRows22[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row17 : fourWide22[17]! =
    expandTree 6 1792 fourRows22[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row18 : fourWide22[18]! =
    expandTree 6 1792 fourRows22[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row19 : fourWide22[19]! =
    expandTree 6 1792 fourRows22[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row20 : fourWide22[20]! =
    expandTree 6 1792 fourRows22[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row21 : fourWide22[21]! =
    expandTree 6 1792 fourRows22[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row22 : fourWide22[22]! =
    expandTree 6 1792 fourRows22[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row23 : fourWide22[23]! =
    expandTree 6 1792 fourRows22[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row24 : fourWide22[24]! =
    expandTree 6 1792 fourRows22[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row25 : fourWide22[25]! =
    expandTree 6 1792 fourRows22[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row26 : fourWide22[26]! =
    expandTree 6 1792 fourRows22[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row27 : fourWide22[27]! =
    expandTree 6 1792 fourRows22[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row28 : fourWide22[28]! =
    expandTree 6 1792 fourRows22[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row29 : fourWide22[29]! =
    expandTree 6 1792 fourRows22[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row30 : fourWide22[30]! =
    expandTree 6 1792 fourRows22[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded22_row31 : fourWide22[31]! =
    expandTree 6 1792 fourRows22[31]! := by decide +kernel

private theorem expanded22 : fourWide22 =
    fourRows22.map (expandTree 6 1792) := by
  change [fourWide22[0]!,
    fourWide22[1]!,
    fourWide22[2]!,
    fourWide22[3]!,
    fourWide22[4]!,
    fourWide22[5]!,
    fourWide22[6]!,
    fourWide22[7]!,
    fourWide22[8]!,
    fourWide22[9]!,
    fourWide22[10]!,
    fourWide22[11]!,
    fourWide22[12]!,
    fourWide22[13]!,
    fourWide22[14]!,
    fourWide22[15]!,
    fourWide22[16]!,
    fourWide22[17]!,
    fourWide22[18]!,
    fourWide22[19]!,
    fourWide22[20]!,
    fourWide22[21]!,
    fourWide22[22]!,
    fourWide22[23]!,
    fourWide22[24]!,
    fourWide22[25]!,
    fourWide22[26]!,
    fourWide22[27]!,
    fourWide22[28]!,
    fourWide22[29]!,
    fourWide22[30]!,
    fourWide22[31]!] =
    [expandTree 6 1792 fourRows22[0]!,
     expandTree 6 1792 fourRows22[1]!,
     expandTree 6 1792 fourRows22[2]!,
     expandTree 6 1792 fourRows22[3]!,
     expandTree 6 1792 fourRows22[4]!,
     expandTree 6 1792 fourRows22[5]!,
     expandTree 6 1792 fourRows22[6]!,
     expandTree 6 1792 fourRows22[7]!,
     expandTree 6 1792 fourRows22[8]!,
     expandTree 6 1792 fourRows22[9]!,
     expandTree 6 1792 fourRows22[10]!,
     expandTree 6 1792 fourRows22[11]!,
     expandTree 6 1792 fourRows22[12]!,
     expandTree 6 1792 fourRows22[13]!,
     expandTree 6 1792 fourRows22[14]!,
     expandTree 6 1792 fourRows22[15]!,
     expandTree 6 1792 fourRows22[16]!,
     expandTree 6 1792 fourRows22[17]!,
     expandTree 6 1792 fourRows22[18]!,
     expandTree 6 1792 fourRows22[19]!,
     expandTree 6 1792 fourRows22[20]!,
     expandTree 6 1792 fourRows22[21]!,
     expandTree 6 1792 fourRows22[22]!,
     expandTree 6 1792 fourRows22[23]!,
     expandTree 6 1792 fourRows22[24]!,
     expandTree 6 1792 fourRows22[25]!,
     expandTree 6 1792 fourRows22[26]!,
     expandTree 6 1792 fourRows22[27]!,
     expandTree 6 1792 fourRows22[28]!,
     expandTree 6 1792 fourRows22[29]!,
     expandTree 6 1792 fourRows22[30]!,
     expandTree 6 1792 fourRows22[31]!]
  rw [expanded22_row00, expanded22_row01, expanded22_row02, expanded22_row03, expanded22_row04, expanded22_row05, expanded22_row06, expanded22_row07, expanded22_row08, expanded22_row09, expanded22_row10, expanded22_row11, expanded22_row12, expanded22_row13, expanded22_row14, expanded22_row15, expanded22_row16, expanded22_row17, expanded22_row18, expanded22_row19, expanded22_row20, expanded22_row21, expanded22_row22, expanded22_row23, expanded22_row24, expanded22_row25, expanded22_row26, expanded22_row27, expanded22_row28, expanded22_row29, expanded22_row30, expanded22_row31]

set_option maxRecDepth 8192 in
private theorem expanded23_row00 : fourWide23[0]! =
    expandTree 6 1792 fourRows23[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row01 : fourWide23[1]! =
    expandTree 6 1792 fourRows23[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row02 : fourWide23[2]! =
    expandTree 6 1792 fourRows23[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row03 : fourWide23[3]! =
    expandTree 6 1792 fourRows23[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row04 : fourWide23[4]! =
    expandTree 6 1792 fourRows23[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row05 : fourWide23[5]! =
    expandTree 6 1792 fourRows23[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row06 : fourWide23[6]! =
    expandTree 6 1792 fourRows23[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row07 : fourWide23[7]! =
    expandTree 6 1792 fourRows23[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row08 : fourWide23[8]! =
    expandTree 6 1792 fourRows23[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row09 : fourWide23[9]! =
    expandTree 6 1792 fourRows23[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row10 : fourWide23[10]! =
    expandTree 6 1792 fourRows23[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row11 : fourWide23[11]! =
    expandTree 6 1792 fourRows23[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row12 : fourWide23[12]! =
    expandTree 6 1792 fourRows23[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row13 : fourWide23[13]! =
    expandTree 6 1792 fourRows23[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row14 : fourWide23[14]! =
    expandTree 6 1792 fourRows23[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row15 : fourWide23[15]! =
    expandTree 6 1792 fourRows23[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row16 : fourWide23[16]! =
    expandTree 6 1792 fourRows23[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row17 : fourWide23[17]! =
    expandTree 6 1792 fourRows23[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row18 : fourWide23[18]! =
    expandTree 6 1792 fourRows23[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row19 : fourWide23[19]! =
    expandTree 6 1792 fourRows23[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row20 : fourWide23[20]! =
    expandTree 6 1792 fourRows23[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row21 : fourWide23[21]! =
    expandTree 6 1792 fourRows23[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row22 : fourWide23[22]! =
    expandTree 6 1792 fourRows23[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row23 : fourWide23[23]! =
    expandTree 6 1792 fourRows23[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row24 : fourWide23[24]! =
    expandTree 6 1792 fourRows23[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row25 : fourWide23[25]! =
    expandTree 6 1792 fourRows23[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row26 : fourWide23[26]! =
    expandTree 6 1792 fourRows23[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row27 : fourWide23[27]! =
    expandTree 6 1792 fourRows23[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row28 : fourWide23[28]! =
    expandTree 6 1792 fourRows23[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row29 : fourWide23[29]! =
    expandTree 6 1792 fourRows23[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row30 : fourWide23[30]! =
    expandTree 6 1792 fourRows23[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded23_row31 : fourWide23[31]! =
    expandTree 6 1792 fourRows23[31]! := by decide +kernel

private theorem expanded23 : fourWide23 =
    fourRows23.map (expandTree 6 1792) := by
  change [fourWide23[0]!,
    fourWide23[1]!,
    fourWide23[2]!,
    fourWide23[3]!,
    fourWide23[4]!,
    fourWide23[5]!,
    fourWide23[6]!,
    fourWide23[7]!,
    fourWide23[8]!,
    fourWide23[9]!,
    fourWide23[10]!,
    fourWide23[11]!,
    fourWide23[12]!,
    fourWide23[13]!,
    fourWide23[14]!,
    fourWide23[15]!,
    fourWide23[16]!,
    fourWide23[17]!,
    fourWide23[18]!,
    fourWide23[19]!,
    fourWide23[20]!,
    fourWide23[21]!,
    fourWide23[22]!,
    fourWide23[23]!,
    fourWide23[24]!,
    fourWide23[25]!,
    fourWide23[26]!,
    fourWide23[27]!,
    fourWide23[28]!,
    fourWide23[29]!,
    fourWide23[30]!,
    fourWide23[31]!] =
    [expandTree 6 1792 fourRows23[0]!,
     expandTree 6 1792 fourRows23[1]!,
     expandTree 6 1792 fourRows23[2]!,
     expandTree 6 1792 fourRows23[3]!,
     expandTree 6 1792 fourRows23[4]!,
     expandTree 6 1792 fourRows23[5]!,
     expandTree 6 1792 fourRows23[6]!,
     expandTree 6 1792 fourRows23[7]!,
     expandTree 6 1792 fourRows23[8]!,
     expandTree 6 1792 fourRows23[9]!,
     expandTree 6 1792 fourRows23[10]!,
     expandTree 6 1792 fourRows23[11]!,
     expandTree 6 1792 fourRows23[12]!,
     expandTree 6 1792 fourRows23[13]!,
     expandTree 6 1792 fourRows23[14]!,
     expandTree 6 1792 fourRows23[15]!,
     expandTree 6 1792 fourRows23[16]!,
     expandTree 6 1792 fourRows23[17]!,
     expandTree 6 1792 fourRows23[18]!,
     expandTree 6 1792 fourRows23[19]!,
     expandTree 6 1792 fourRows23[20]!,
     expandTree 6 1792 fourRows23[21]!,
     expandTree 6 1792 fourRows23[22]!,
     expandTree 6 1792 fourRows23[23]!,
     expandTree 6 1792 fourRows23[24]!,
     expandTree 6 1792 fourRows23[25]!,
     expandTree 6 1792 fourRows23[26]!,
     expandTree 6 1792 fourRows23[27]!,
     expandTree 6 1792 fourRows23[28]!,
     expandTree 6 1792 fourRows23[29]!,
     expandTree 6 1792 fourRows23[30]!,
     expandTree 6 1792 fourRows23[31]!]
  rw [expanded23_row00, expanded23_row01, expanded23_row02, expanded23_row03, expanded23_row04, expanded23_row05, expanded23_row06, expanded23_row07, expanded23_row08, expanded23_row09, expanded23_row10, expanded23_row11, expanded23_row12, expanded23_row13, expanded23_row14, expanded23_row15, expanded23_row16, expanded23_row17, expanded23_row18, expanded23_row19, expanded23_row20, expanded23_row21, expanded23_row22, expanded23_row23, expanded23_row24, expanded23_row25, expanded23_row26, expanded23_row27, expanded23_row28, expanded23_row29, expanded23_row30, expanded23_row31]

set_option maxRecDepth 8192 in
private theorem expanded24_row00 : fourWide24[0]! =
    expandTree 6 1792 fourRows24[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row01 : fourWide24[1]! =
    expandTree 6 1792 fourRows24[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row02 : fourWide24[2]! =
    expandTree 6 1792 fourRows24[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row03 : fourWide24[3]! =
    expandTree 6 1792 fourRows24[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row04 : fourWide24[4]! =
    expandTree 6 1792 fourRows24[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row05 : fourWide24[5]! =
    expandTree 6 1792 fourRows24[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row06 : fourWide24[6]! =
    expandTree 6 1792 fourRows24[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row07 : fourWide24[7]! =
    expandTree 6 1792 fourRows24[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row08 : fourWide24[8]! =
    expandTree 6 1792 fourRows24[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row09 : fourWide24[9]! =
    expandTree 6 1792 fourRows24[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row10 : fourWide24[10]! =
    expandTree 6 1792 fourRows24[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row11 : fourWide24[11]! =
    expandTree 6 1792 fourRows24[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row12 : fourWide24[12]! =
    expandTree 6 1792 fourRows24[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row13 : fourWide24[13]! =
    expandTree 6 1792 fourRows24[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row14 : fourWide24[14]! =
    expandTree 6 1792 fourRows24[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row15 : fourWide24[15]! =
    expandTree 6 1792 fourRows24[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row16 : fourWide24[16]! =
    expandTree 6 1792 fourRows24[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row17 : fourWide24[17]! =
    expandTree 6 1792 fourRows24[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row18 : fourWide24[18]! =
    expandTree 6 1792 fourRows24[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row19 : fourWide24[19]! =
    expandTree 6 1792 fourRows24[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row20 : fourWide24[20]! =
    expandTree 6 1792 fourRows24[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row21 : fourWide24[21]! =
    expandTree 6 1792 fourRows24[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row22 : fourWide24[22]! =
    expandTree 6 1792 fourRows24[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row23 : fourWide24[23]! =
    expandTree 6 1792 fourRows24[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row24 : fourWide24[24]! =
    expandTree 6 1792 fourRows24[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row25 : fourWide24[25]! =
    expandTree 6 1792 fourRows24[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row26 : fourWide24[26]! =
    expandTree 6 1792 fourRows24[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row27 : fourWide24[27]! =
    expandTree 6 1792 fourRows24[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row28 : fourWide24[28]! =
    expandTree 6 1792 fourRows24[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row29 : fourWide24[29]! =
    expandTree 6 1792 fourRows24[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row30 : fourWide24[30]! =
    expandTree 6 1792 fourRows24[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded24_row31 : fourWide24[31]! =
    expandTree 6 1792 fourRows24[31]! := by decide +kernel

private theorem expanded24 : fourWide24 =
    fourRows24.map (expandTree 6 1792) := by
  change [fourWide24[0]!,
    fourWide24[1]!,
    fourWide24[2]!,
    fourWide24[3]!,
    fourWide24[4]!,
    fourWide24[5]!,
    fourWide24[6]!,
    fourWide24[7]!,
    fourWide24[8]!,
    fourWide24[9]!,
    fourWide24[10]!,
    fourWide24[11]!,
    fourWide24[12]!,
    fourWide24[13]!,
    fourWide24[14]!,
    fourWide24[15]!,
    fourWide24[16]!,
    fourWide24[17]!,
    fourWide24[18]!,
    fourWide24[19]!,
    fourWide24[20]!,
    fourWide24[21]!,
    fourWide24[22]!,
    fourWide24[23]!,
    fourWide24[24]!,
    fourWide24[25]!,
    fourWide24[26]!,
    fourWide24[27]!,
    fourWide24[28]!,
    fourWide24[29]!,
    fourWide24[30]!,
    fourWide24[31]!] =
    [expandTree 6 1792 fourRows24[0]!,
     expandTree 6 1792 fourRows24[1]!,
     expandTree 6 1792 fourRows24[2]!,
     expandTree 6 1792 fourRows24[3]!,
     expandTree 6 1792 fourRows24[4]!,
     expandTree 6 1792 fourRows24[5]!,
     expandTree 6 1792 fourRows24[6]!,
     expandTree 6 1792 fourRows24[7]!,
     expandTree 6 1792 fourRows24[8]!,
     expandTree 6 1792 fourRows24[9]!,
     expandTree 6 1792 fourRows24[10]!,
     expandTree 6 1792 fourRows24[11]!,
     expandTree 6 1792 fourRows24[12]!,
     expandTree 6 1792 fourRows24[13]!,
     expandTree 6 1792 fourRows24[14]!,
     expandTree 6 1792 fourRows24[15]!,
     expandTree 6 1792 fourRows24[16]!,
     expandTree 6 1792 fourRows24[17]!,
     expandTree 6 1792 fourRows24[18]!,
     expandTree 6 1792 fourRows24[19]!,
     expandTree 6 1792 fourRows24[20]!,
     expandTree 6 1792 fourRows24[21]!,
     expandTree 6 1792 fourRows24[22]!,
     expandTree 6 1792 fourRows24[23]!,
     expandTree 6 1792 fourRows24[24]!,
     expandTree 6 1792 fourRows24[25]!,
     expandTree 6 1792 fourRows24[26]!,
     expandTree 6 1792 fourRows24[27]!,
     expandTree 6 1792 fourRows24[28]!,
     expandTree 6 1792 fourRows24[29]!,
     expandTree 6 1792 fourRows24[30]!,
     expandTree 6 1792 fourRows24[31]!]
  rw [expanded24_row00, expanded24_row01, expanded24_row02, expanded24_row03, expanded24_row04, expanded24_row05, expanded24_row06, expanded24_row07, expanded24_row08, expanded24_row09, expanded24_row10, expanded24_row11, expanded24_row12, expanded24_row13, expanded24_row14, expanded24_row15, expanded24_row16, expanded24_row17, expanded24_row18, expanded24_row19, expanded24_row20, expanded24_row21, expanded24_row22, expanded24_row23, expanded24_row24, expanded24_row25, expanded24_row26, expanded24_row27, expanded24_row28, expanded24_row29, expanded24_row30, expanded24_row31]

set_option maxRecDepth 8192 in
private theorem expanded25_row00 : fourWide25[0]! =
    expandTree 6 1792 fourRows25[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row01 : fourWide25[1]! =
    expandTree 6 1792 fourRows25[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row02 : fourWide25[2]! =
    expandTree 6 1792 fourRows25[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row03 : fourWide25[3]! =
    expandTree 6 1792 fourRows25[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row04 : fourWide25[4]! =
    expandTree 6 1792 fourRows25[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row05 : fourWide25[5]! =
    expandTree 6 1792 fourRows25[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row06 : fourWide25[6]! =
    expandTree 6 1792 fourRows25[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row07 : fourWide25[7]! =
    expandTree 6 1792 fourRows25[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row08 : fourWide25[8]! =
    expandTree 6 1792 fourRows25[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row09 : fourWide25[9]! =
    expandTree 6 1792 fourRows25[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row10 : fourWide25[10]! =
    expandTree 6 1792 fourRows25[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row11 : fourWide25[11]! =
    expandTree 6 1792 fourRows25[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row12 : fourWide25[12]! =
    expandTree 6 1792 fourRows25[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row13 : fourWide25[13]! =
    expandTree 6 1792 fourRows25[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row14 : fourWide25[14]! =
    expandTree 6 1792 fourRows25[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row15 : fourWide25[15]! =
    expandTree 6 1792 fourRows25[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row16 : fourWide25[16]! =
    expandTree 6 1792 fourRows25[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row17 : fourWide25[17]! =
    expandTree 6 1792 fourRows25[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row18 : fourWide25[18]! =
    expandTree 6 1792 fourRows25[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row19 : fourWide25[19]! =
    expandTree 6 1792 fourRows25[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row20 : fourWide25[20]! =
    expandTree 6 1792 fourRows25[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row21 : fourWide25[21]! =
    expandTree 6 1792 fourRows25[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row22 : fourWide25[22]! =
    expandTree 6 1792 fourRows25[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row23 : fourWide25[23]! =
    expandTree 6 1792 fourRows25[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row24 : fourWide25[24]! =
    expandTree 6 1792 fourRows25[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row25 : fourWide25[25]! =
    expandTree 6 1792 fourRows25[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row26 : fourWide25[26]! =
    expandTree 6 1792 fourRows25[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row27 : fourWide25[27]! =
    expandTree 6 1792 fourRows25[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row28 : fourWide25[28]! =
    expandTree 6 1792 fourRows25[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row29 : fourWide25[29]! =
    expandTree 6 1792 fourRows25[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row30 : fourWide25[30]! =
    expandTree 6 1792 fourRows25[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded25_row31 : fourWide25[31]! =
    expandTree 6 1792 fourRows25[31]! := by decide +kernel

private theorem expanded25 : fourWide25 =
    fourRows25.map (expandTree 6 1792) := by
  change [fourWide25[0]!,
    fourWide25[1]!,
    fourWide25[2]!,
    fourWide25[3]!,
    fourWide25[4]!,
    fourWide25[5]!,
    fourWide25[6]!,
    fourWide25[7]!,
    fourWide25[8]!,
    fourWide25[9]!,
    fourWide25[10]!,
    fourWide25[11]!,
    fourWide25[12]!,
    fourWide25[13]!,
    fourWide25[14]!,
    fourWide25[15]!,
    fourWide25[16]!,
    fourWide25[17]!,
    fourWide25[18]!,
    fourWide25[19]!,
    fourWide25[20]!,
    fourWide25[21]!,
    fourWide25[22]!,
    fourWide25[23]!,
    fourWide25[24]!,
    fourWide25[25]!,
    fourWide25[26]!,
    fourWide25[27]!,
    fourWide25[28]!,
    fourWide25[29]!,
    fourWide25[30]!,
    fourWide25[31]!] =
    [expandTree 6 1792 fourRows25[0]!,
     expandTree 6 1792 fourRows25[1]!,
     expandTree 6 1792 fourRows25[2]!,
     expandTree 6 1792 fourRows25[3]!,
     expandTree 6 1792 fourRows25[4]!,
     expandTree 6 1792 fourRows25[5]!,
     expandTree 6 1792 fourRows25[6]!,
     expandTree 6 1792 fourRows25[7]!,
     expandTree 6 1792 fourRows25[8]!,
     expandTree 6 1792 fourRows25[9]!,
     expandTree 6 1792 fourRows25[10]!,
     expandTree 6 1792 fourRows25[11]!,
     expandTree 6 1792 fourRows25[12]!,
     expandTree 6 1792 fourRows25[13]!,
     expandTree 6 1792 fourRows25[14]!,
     expandTree 6 1792 fourRows25[15]!,
     expandTree 6 1792 fourRows25[16]!,
     expandTree 6 1792 fourRows25[17]!,
     expandTree 6 1792 fourRows25[18]!,
     expandTree 6 1792 fourRows25[19]!,
     expandTree 6 1792 fourRows25[20]!,
     expandTree 6 1792 fourRows25[21]!,
     expandTree 6 1792 fourRows25[22]!,
     expandTree 6 1792 fourRows25[23]!,
     expandTree 6 1792 fourRows25[24]!,
     expandTree 6 1792 fourRows25[25]!,
     expandTree 6 1792 fourRows25[26]!,
     expandTree 6 1792 fourRows25[27]!,
     expandTree 6 1792 fourRows25[28]!,
     expandTree 6 1792 fourRows25[29]!,
     expandTree 6 1792 fourRows25[30]!,
     expandTree 6 1792 fourRows25[31]!]
  rw [expanded25_row00, expanded25_row01, expanded25_row02, expanded25_row03, expanded25_row04, expanded25_row05, expanded25_row06, expanded25_row07, expanded25_row08, expanded25_row09, expanded25_row10, expanded25_row11, expanded25_row12, expanded25_row13, expanded25_row14, expanded25_row15, expanded25_row16, expanded25_row17, expanded25_row18, expanded25_row19, expanded25_row20, expanded25_row21, expanded25_row22, expanded25_row23, expanded25_row24, expanded25_row25, expanded25_row26, expanded25_row27, expanded25_row28, expanded25_row29, expanded25_row30, expanded25_row31]

set_option maxRecDepth 8192 in
private theorem expanded26_row00 : fourWide26[0]! =
    expandTree 6 1792 fourRows26[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row01 : fourWide26[1]! =
    expandTree 6 1792 fourRows26[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row02 : fourWide26[2]! =
    expandTree 6 1792 fourRows26[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row03 : fourWide26[3]! =
    expandTree 6 1792 fourRows26[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row04 : fourWide26[4]! =
    expandTree 6 1792 fourRows26[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row05 : fourWide26[5]! =
    expandTree 6 1792 fourRows26[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row06 : fourWide26[6]! =
    expandTree 6 1792 fourRows26[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row07 : fourWide26[7]! =
    expandTree 6 1792 fourRows26[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row08 : fourWide26[8]! =
    expandTree 6 1792 fourRows26[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row09 : fourWide26[9]! =
    expandTree 6 1792 fourRows26[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row10 : fourWide26[10]! =
    expandTree 6 1792 fourRows26[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row11 : fourWide26[11]! =
    expandTree 6 1792 fourRows26[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row12 : fourWide26[12]! =
    expandTree 6 1792 fourRows26[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row13 : fourWide26[13]! =
    expandTree 6 1792 fourRows26[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row14 : fourWide26[14]! =
    expandTree 6 1792 fourRows26[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row15 : fourWide26[15]! =
    expandTree 6 1792 fourRows26[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row16 : fourWide26[16]! =
    expandTree 6 1792 fourRows26[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row17 : fourWide26[17]! =
    expandTree 6 1792 fourRows26[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row18 : fourWide26[18]! =
    expandTree 6 1792 fourRows26[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row19 : fourWide26[19]! =
    expandTree 6 1792 fourRows26[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row20 : fourWide26[20]! =
    expandTree 6 1792 fourRows26[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row21 : fourWide26[21]! =
    expandTree 6 1792 fourRows26[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row22 : fourWide26[22]! =
    expandTree 6 1792 fourRows26[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row23 : fourWide26[23]! =
    expandTree 6 1792 fourRows26[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row24 : fourWide26[24]! =
    expandTree 6 1792 fourRows26[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row25 : fourWide26[25]! =
    expandTree 6 1792 fourRows26[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row26 : fourWide26[26]! =
    expandTree 6 1792 fourRows26[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row27 : fourWide26[27]! =
    expandTree 6 1792 fourRows26[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row28 : fourWide26[28]! =
    expandTree 6 1792 fourRows26[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row29 : fourWide26[29]! =
    expandTree 6 1792 fourRows26[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row30 : fourWide26[30]! =
    expandTree 6 1792 fourRows26[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded26_row31 : fourWide26[31]! =
    expandTree 6 1792 fourRows26[31]! := by decide +kernel

private theorem expanded26 : fourWide26 =
    fourRows26.map (expandTree 6 1792) := by
  change [fourWide26[0]!,
    fourWide26[1]!,
    fourWide26[2]!,
    fourWide26[3]!,
    fourWide26[4]!,
    fourWide26[5]!,
    fourWide26[6]!,
    fourWide26[7]!,
    fourWide26[8]!,
    fourWide26[9]!,
    fourWide26[10]!,
    fourWide26[11]!,
    fourWide26[12]!,
    fourWide26[13]!,
    fourWide26[14]!,
    fourWide26[15]!,
    fourWide26[16]!,
    fourWide26[17]!,
    fourWide26[18]!,
    fourWide26[19]!,
    fourWide26[20]!,
    fourWide26[21]!,
    fourWide26[22]!,
    fourWide26[23]!,
    fourWide26[24]!,
    fourWide26[25]!,
    fourWide26[26]!,
    fourWide26[27]!,
    fourWide26[28]!,
    fourWide26[29]!,
    fourWide26[30]!,
    fourWide26[31]!] =
    [expandTree 6 1792 fourRows26[0]!,
     expandTree 6 1792 fourRows26[1]!,
     expandTree 6 1792 fourRows26[2]!,
     expandTree 6 1792 fourRows26[3]!,
     expandTree 6 1792 fourRows26[4]!,
     expandTree 6 1792 fourRows26[5]!,
     expandTree 6 1792 fourRows26[6]!,
     expandTree 6 1792 fourRows26[7]!,
     expandTree 6 1792 fourRows26[8]!,
     expandTree 6 1792 fourRows26[9]!,
     expandTree 6 1792 fourRows26[10]!,
     expandTree 6 1792 fourRows26[11]!,
     expandTree 6 1792 fourRows26[12]!,
     expandTree 6 1792 fourRows26[13]!,
     expandTree 6 1792 fourRows26[14]!,
     expandTree 6 1792 fourRows26[15]!,
     expandTree 6 1792 fourRows26[16]!,
     expandTree 6 1792 fourRows26[17]!,
     expandTree 6 1792 fourRows26[18]!,
     expandTree 6 1792 fourRows26[19]!,
     expandTree 6 1792 fourRows26[20]!,
     expandTree 6 1792 fourRows26[21]!,
     expandTree 6 1792 fourRows26[22]!,
     expandTree 6 1792 fourRows26[23]!,
     expandTree 6 1792 fourRows26[24]!,
     expandTree 6 1792 fourRows26[25]!,
     expandTree 6 1792 fourRows26[26]!,
     expandTree 6 1792 fourRows26[27]!,
     expandTree 6 1792 fourRows26[28]!,
     expandTree 6 1792 fourRows26[29]!,
     expandTree 6 1792 fourRows26[30]!,
     expandTree 6 1792 fourRows26[31]!]
  rw [expanded26_row00, expanded26_row01, expanded26_row02, expanded26_row03, expanded26_row04, expanded26_row05, expanded26_row06, expanded26_row07, expanded26_row08, expanded26_row09, expanded26_row10, expanded26_row11, expanded26_row12, expanded26_row13, expanded26_row14, expanded26_row15, expanded26_row16, expanded26_row17, expanded26_row18, expanded26_row19, expanded26_row20, expanded26_row21, expanded26_row22, expanded26_row23, expanded26_row24, expanded26_row25, expanded26_row26, expanded26_row27, expanded26_row28, expanded26_row29, expanded26_row30, expanded26_row31]

set_option maxRecDepth 8192 in
private theorem expanded27_row00 : fourWide27[0]! =
    expandTree 6 1792 fourRows27[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row01 : fourWide27[1]! =
    expandTree 6 1792 fourRows27[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row02 : fourWide27[2]! =
    expandTree 6 1792 fourRows27[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row03 : fourWide27[3]! =
    expandTree 6 1792 fourRows27[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row04 : fourWide27[4]! =
    expandTree 6 1792 fourRows27[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row05 : fourWide27[5]! =
    expandTree 6 1792 fourRows27[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row06 : fourWide27[6]! =
    expandTree 6 1792 fourRows27[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row07 : fourWide27[7]! =
    expandTree 6 1792 fourRows27[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row08 : fourWide27[8]! =
    expandTree 6 1792 fourRows27[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row09 : fourWide27[9]! =
    expandTree 6 1792 fourRows27[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row10 : fourWide27[10]! =
    expandTree 6 1792 fourRows27[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row11 : fourWide27[11]! =
    expandTree 6 1792 fourRows27[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row12 : fourWide27[12]! =
    expandTree 6 1792 fourRows27[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row13 : fourWide27[13]! =
    expandTree 6 1792 fourRows27[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row14 : fourWide27[14]! =
    expandTree 6 1792 fourRows27[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row15 : fourWide27[15]! =
    expandTree 6 1792 fourRows27[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row16 : fourWide27[16]! =
    expandTree 6 1792 fourRows27[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row17 : fourWide27[17]! =
    expandTree 6 1792 fourRows27[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row18 : fourWide27[18]! =
    expandTree 6 1792 fourRows27[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row19 : fourWide27[19]! =
    expandTree 6 1792 fourRows27[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row20 : fourWide27[20]! =
    expandTree 6 1792 fourRows27[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row21 : fourWide27[21]! =
    expandTree 6 1792 fourRows27[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row22 : fourWide27[22]! =
    expandTree 6 1792 fourRows27[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row23 : fourWide27[23]! =
    expandTree 6 1792 fourRows27[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row24 : fourWide27[24]! =
    expandTree 6 1792 fourRows27[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row25 : fourWide27[25]! =
    expandTree 6 1792 fourRows27[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row26 : fourWide27[26]! =
    expandTree 6 1792 fourRows27[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row27 : fourWide27[27]! =
    expandTree 6 1792 fourRows27[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row28 : fourWide27[28]! =
    expandTree 6 1792 fourRows27[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row29 : fourWide27[29]! =
    expandTree 6 1792 fourRows27[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row30 : fourWide27[30]! =
    expandTree 6 1792 fourRows27[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded27_row31 : fourWide27[31]! =
    expandTree 6 1792 fourRows27[31]! := by decide +kernel

private theorem expanded27 : fourWide27 =
    fourRows27.map (expandTree 6 1792) := by
  change [fourWide27[0]!,
    fourWide27[1]!,
    fourWide27[2]!,
    fourWide27[3]!,
    fourWide27[4]!,
    fourWide27[5]!,
    fourWide27[6]!,
    fourWide27[7]!,
    fourWide27[8]!,
    fourWide27[9]!,
    fourWide27[10]!,
    fourWide27[11]!,
    fourWide27[12]!,
    fourWide27[13]!,
    fourWide27[14]!,
    fourWide27[15]!,
    fourWide27[16]!,
    fourWide27[17]!,
    fourWide27[18]!,
    fourWide27[19]!,
    fourWide27[20]!,
    fourWide27[21]!,
    fourWide27[22]!,
    fourWide27[23]!,
    fourWide27[24]!,
    fourWide27[25]!,
    fourWide27[26]!,
    fourWide27[27]!,
    fourWide27[28]!,
    fourWide27[29]!,
    fourWide27[30]!,
    fourWide27[31]!] =
    [expandTree 6 1792 fourRows27[0]!,
     expandTree 6 1792 fourRows27[1]!,
     expandTree 6 1792 fourRows27[2]!,
     expandTree 6 1792 fourRows27[3]!,
     expandTree 6 1792 fourRows27[4]!,
     expandTree 6 1792 fourRows27[5]!,
     expandTree 6 1792 fourRows27[6]!,
     expandTree 6 1792 fourRows27[7]!,
     expandTree 6 1792 fourRows27[8]!,
     expandTree 6 1792 fourRows27[9]!,
     expandTree 6 1792 fourRows27[10]!,
     expandTree 6 1792 fourRows27[11]!,
     expandTree 6 1792 fourRows27[12]!,
     expandTree 6 1792 fourRows27[13]!,
     expandTree 6 1792 fourRows27[14]!,
     expandTree 6 1792 fourRows27[15]!,
     expandTree 6 1792 fourRows27[16]!,
     expandTree 6 1792 fourRows27[17]!,
     expandTree 6 1792 fourRows27[18]!,
     expandTree 6 1792 fourRows27[19]!,
     expandTree 6 1792 fourRows27[20]!,
     expandTree 6 1792 fourRows27[21]!,
     expandTree 6 1792 fourRows27[22]!,
     expandTree 6 1792 fourRows27[23]!,
     expandTree 6 1792 fourRows27[24]!,
     expandTree 6 1792 fourRows27[25]!,
     expandTree 6 1792 fourRows27[26]!,
     expandTree 6 1792 fourRows27[27]!,
     expandTree 6 1792 fourRows27[28]!,
     expandTree 6 1792 fourRows27[29]!,
     expandTree 6 1792 fourRows27[30]!,
     expandTree 6 1792 fourRows27[31]!]
  rw [expanded27_row00, expanded27_row01, expanded27_row02, expanded27_row03, expanded27_row04, expanded27_row05, expanded27_row06, expanded27_row07, expanded27_row08, expanded27_row09, expanded27_row10, expanded27_row11, expanded27_row12, expanded27_row13, expanded27_row14, expanded27_row15, expanded27_row16, expanded27_row17, expanded27_row18, expanded27_row19, expanded27_row20, expanded27_row21, expanded27_row22, expanded27_row23, expanded27_row24, expanded27_row25, expanded27_row26, expanded27_row27, expanded27_row28, expanded27_row29, expanded27_row30, expanded27_row31]

set_option maxRecDepth 8192 in
private theorem expanded28_row00 : fourWide28[0]! =
    expandTree 6 1792 fourRows28[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row01 : fourWide28[1]! =
    expandTree 6 1792 fourRows28[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row02 : fourWide28[2]! =
    expandTree 6 1792 fourRows28[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row03 : fourWide28[3]! =
    expandTree 6 1792 fourRows28[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row04 : fourWide28[4]! =
    expandTree 6 1792 fourRows28[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row05 : fourWide28[5]! =
    expandTree 6 1792 fourRows28[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row06 : fourWide28[6]! =
    expandTree 6 1792 fourRows28[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row07 : fourWide28[7]! =
    expandTree 6 1792 fourRows28[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row08 : fourWide28[8]! =
    expandTree 6 1792 fourRows28[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row09 : fourWide28[9]! =
    expandTree 6 1792 fourRows28[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row10 : fourWide28[10]! =
    expandTree 6 1792 fourRows28[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row11 : fourWide28[11]! =
    expandTree 6 1792 fourRows28[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row12 : fourWide28[12]! =
    expandTree 6 1792 fourRows28[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row13 : fourWide28[13]! =
    expandTree 6 1792 fourRows28[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row14 : fourWide28[14]! =
    expandTree 6 1792 fourRows28[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row15 : fourWide28[15]! =
    expandTree 6 1792 fourRows28[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row16 : fourWide28[16]! =
    expandTree 6 1792 fourRows28[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row17 : fourWide28[17]! =
    expandTree 6 1792 fourRows28[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row18 : fourWide28[18]! =
    expandTree 6 1792 fourRows28[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row19 : fourWide28[19]! =
    expandTree 6 1792 fourRows28[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row20 : fourWide28[20]! =
    expandTree 6 1792 fourRows28[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row21 : fourWide28[21]! =
    expandTree 6 1792 fourRows28[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row22 : fourWide28[22]! =
    expandTree 6 1792 fourRows28[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row23 : fourWide28[23]! =
    expandTree 6 1792 fourRows28[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row24 : fourWide28[24]! =
    expandTree 6 1792 fourRows28[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row25 : fourWide28[25]! =
    expandTree 6 1792 fourRows28[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row26 : fourWide28[26]! =
    expandTree 6 1792 fourRows28[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row27 : fourWide28[27]! =
    expandTree 6 1792 fourRows28[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row28 : fourWide28[28]! =
    expandTree 6 1792 fourRows28[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row29 : fourWide28[29]! =
    expandTree 6 1792 fourRows28[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row30 : fourWide28[30]! =
    expandTree 6 1792 fourRows28[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded28_row31 : fourWide28[31]! =
    expandTree 6 1792 fourRows28[31]! := by decide +kernel

private theorem expanded28 : fourWide28 =
    fourRows28.map (expandTree 6 1792) := by
  change [fourWide28[0]!,
    fourWide28[1]!,
    fourWide28[2]!,
    fourWide28[3]!,
    fourWide28[4]!,
    fourWide28[5]!,
    fourWide28[6]!,
    fourWide28[7]!,
    fourWide28[8]!,
    fourWide28[9]!,
    fourWide28[10]!,
    fourWide28[11]!,
    fourWide28[12]!,
    fourWide28[13]!,
    fourWide28[14]!,
    fourWide28[15]!,
    fourWide28[16]!,
    fourWide28[17]!,
    fourWide28[18]!,
    fourWide28[19]!,
    fourWide28[20]!,
    fourWide28[21]!,
    fourWide28[22]!,
    fourWide28[23]!,
    fourWide28[24]!,
    fourWide28[25]!,
    fourWide28[26]!,
    fourWide28[27]!,
    fourWide28[28]!,
    fourWide28[29]!,
    fourWide28[30]!,
    fourWide28[31]!] =
    [expandTree 6 1792 fourRows28[0]!,
     expandTree 6 1792 fourRows28[1]!,
     expandTree 6 1792 fourRows28[2]!,
     expandTree 6 1792 fourRows28[3]!,
     expandTree 6 1792 fourRows28[4]!,
     expandTree 6 1792 fourRows28[5]!,
     expandTree 6 1792 fourRows28[6]!,
     expandTree 6 1792 fourRows28[7]!,
     expandTree 6 1792 fourRows28[8]!,
     expandTree 6 1792 fourRows28[9]!,
     expandTree 6 1792 fourRows28[10]!,
     expandTree 6 1792 fourRows28[11]!,
     expandTree 6 1792 fourRows28[12]!,
     expandTree 6 1792 fourRows28[13]!,
     expandTree 6 1792 fourRows28[14]!,
     expandTree 6 1792 fourRows28[15]!,
     expandTree 6 1792 fourRows28[16]!,
     expandTree 6 1792 fourRows28[17]!,
     expandTree 6 1792 fourRows28[18]!,
     expandTree 6 1792 fourRows28[19]!,
     expandTree 6 1792 fourRows28[20]!,
     expandTree 6 1792 fourRows28[21]!,
     expandTree 6 1792 fourRows28[22]!,
     expandTree 6 1792 fourRows28[23]!,
     expandTree 6 1792 fourRows28[24]!,
     expandTree 6 1792 fourRows28[25]!,
     expandTree 6 1792 fourRows28[26]!,
     expandTree 6 1792 fourRows28[27]!,
     expandTree 6 1792 fourRows28[28]!,
     expandTree 6 1792 fourRows28[29]!,
     expandTree 6 1792 fourRows28[30]!,
     expandTree 6 1792 fourRows28[31]!]
  rw [expanded28_row00, expanded28_row01, expanded28_row02, expanded28_row03, expanded28_row04, expanded28_row05, expanded28_row06, expanded28_row07, expanded28_row08, expanded28_row09, expanded28_row10, expanded28_row11, expanded28_row12, expanded28_row13, expanded28_row14, expanded28_row15, expanded28_row16, expanded28_row17, expanded28_row18, expanded28_row19, expanded28_row20, expanded28_row21, expanded28_row22, expanded28_row23, expanded28_row24, expanded28_row25, expanded28_row26, expanded28_row27, expanded28_row28, expanded28_row29, expanded28_row30, expanded28_row31]

set_option maxRecDepth 8192 in
private theorem expanded29_row00 : fourWide29[0]! =
    expandTree 6 1792 fourRows29[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row01 : fourWide29[1]! =
    expandTree 6 1792 fourRows29[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row02 : fourWide29[2]! =
    expandTree 6 1792 fourRows29[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row03 : fourWide29[3]! =
    expandTree 6 1792 fourRows29[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row04 : fourWide29[4]! =
    expandTree 6 1792 fourRows29[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row05 : fourWide29[5]! =
    expandTree 6 1792 fourRows29[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row06 : fourWide29[6]! =
    expandTree 6 1792 fourRows29[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row07 : fourWide29[7]! =
    expandTree 6 1792 fourRows29[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row08 : fourWide29[8]! =
    expandTree 6 1792 fourRows29[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row09 : fourWide29[9]! =
    expandTree 6 1792 fourRows29[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row10 : fourWide29[10]! =
    expandTree 6 1792 fourRows29[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row11 : fourWide29[11]! =
    expandTree 6 1792 fourRows29[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row12 : fourWide29[12]! =
    expandTree 6 1792 fourRows29[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row13 : fourWide29[13]! =
    expandTree 6 1792 fourRows29[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row14 : fourWide29[14]! =
    expandTree 6 1792 fourRows29[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row15 : fourWide29[15]! =
    expandTree 6 1792 fourRows29[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row16 : fourWide29[16]! =
    expandTree 6 1792 fourRows29[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row17 : fourWide29[17]! =
    expandTree 6 1792 fourRows29[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row18 : fourWide29[18]! =
    expandTree 6 1792 fourRows29[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row19 : fourWide29[19]! =
    expandTree 6 1792 fourRows29[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row20 : fourWide29[20]! =
    expandTree 6 1792 fourRows29[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row21 : fourWide29[21]! =
    expandTree 6 1792 fourRows29[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row22 : fourWide29[22]! =
    expandTree 6 1792 fourRows29[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row23 : fourWide29[23]! =
    expandTree 6 1792 fourRows29[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row24 : fourWide29[24]! =
    expandTree 6 1792 fourRows29[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row25 : fourWide29[25]! =
    expandTree 6 1792 fourRows29[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row26 : fourWide29[26]! =
    expandTree 6 1792 fourRows29[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row27 : fourWide29[27]! =
    expandTree 6 1792 fourRows29[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row28 : fourWide29[28]! =
    expandTree 6 1792 fourRows29[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row29 : fourWide29[29]! =
    expandTree 6 1792 fourRows29[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row30 : fourWide29[30]! =
    expandTree 6 1792 fourRows29[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded29_row31 : fourWide29[31]! =
    expandTree 6 1792 fourRows29[31]! := by decide +kernel

private theorem expanded29 : fourWide29 =
    fourRows29.map (expandTree 6 1792) := by
  change [fourWide29[0]!,
    fourWide29[1]!,
    fourWide29[2]!,
    fourWide29[3]!,
    fourWide29[4]!,
    fourWide29[5]!,
    fourWide29[6]!,
    fourWide29[7]!,
    fourWide29[8]!,
    fourWide29[9]!,
    fourWide29[10]!,
    fourWide29[11]!,
    fourWide29[12]!,
    fourWide29[13]!,
    fourWide29[14]!,
    fourWide29[15]!,
    fourWide29[16]!,
    fourWide29[17]!,
    fourWide29[18]!,
    fourWide29[19]!,
    fourWide29[20]!,
    fourWide29[21]!,
    fourWide29[22]!,
    fourWide29[23]!,
    fourWide29[24]!,
    fourWide29[25]!,
    fourWide29[26]!,
    fourWide29[27]!,
    fourWide29[28]!,
    fourWide29[29]!,
    fourWide29[30]!,
    fourWide29[31]!] =
    [expandTree 6 1792 fourRows29[0]!,
     expandTree 6 1792 fourRows29[1]!,
     expandTree 6 1792 fourRows29[2]!,
     expandTree 6 1792 fourRows29[3]!,
     expandTree 6 1792 fourRows29[4]!,
     expandTree 6 1792 fourRows29[5]!,
     expandTree 6 1792 fourRows29[6]!,
     expandTree 6 1792 fourRows29[7]!,
     expandTree 6 1792 fourRows29[8]!,
     expandTree 6 1792 fourRows29[9]!,
     expandTree 6 1792 fourRows29[10]!,
     expandTree 6 1792 fourRows29[11]!,
     expandTree 6 1792 fourRows29[12]!,
     expandTree 6 1792 fourRows29[13]!,
     expandTree 6 1792 fourRows29[14]!,
     expandTree 6 1792 fourRows29[15]!,
     expandTree 6 1792 fourRows29[16]!,
     expandTree 6 1792 fourRows29[17]!,
     expandTree 6 1792 fourRows29[18]!,
     expandTree 6 1792 fourRows29[19]!,
     expandTree 6 1792 fourRows29[20]!,
     expandTree 6 1792 fourRows29[21]!,
     expandTree 6 1792 fourRows29[22]!,
     expandTree 6 1792 fourRows29[23]!,
     expandTree 6 1792 fourRows29[24]!,
     expandTree 6 1792 fourRows29[25]!,
     expandTree 6 1792 fourRows29[26]!,
     expandTree 6 1792 fourRows29[27]!,
     expandTree 6 1792 fourRows29[28]!,
     expandTree 6 1792 fourRows29[29]!,
     expandTree 6 1792 fourRows29[30]!,
     expandTree 6 1792 fourRows29[31]!]
  rw [expanded29_row00, expanded29_row01, expanded29_row02, expanded29_row03, expanded29_row04, expanded29_row05, expanded29_row06, expanded29_row07, expanded29_row08, expanded29_row09, expanded29_row10, expanded29_row11, expanded29_row12, expanded29_row13, expanded29_row14, expanded29_row15, expanded29_row16, expanded29_row17, expanded29_row18, expanded29_row19, expanded29_row20, expanded29_row21, expanded29_row22, expanded29_row23, expanded29_row24, expanded29_row25, expanded29_row26, expanded29_row27, expanded29_row28, expanded29_row29, expanded29_row30, expanded29_row31]

set_option maxRecDepth 8192 in
private theorem expanded30_row00 : fourWide30[0]! =
    expandTree 6 1792 fourRows30[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row01 : fourWide30[1]! =
    expandTree 6 1792 fourRows30[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row02 : fourWide30[2]! =
    expandTree 6 1792 fourRows30[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row03 : fourWide30[3]! =
    expandTree 6 1792 fourRows30[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row04 : fourWide30[4]! =
    expandTree 6 1792 fourRows30[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row05 : fourWide30[5]! =
    expandTree 6 1792 fourRows30[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row06 : fourWide30[6]! =
    expandTree 6 1792 fourRows30[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row07 : fourWide30[7]! =
    expandTree 6 1792 fourRows30[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row08 : fourWide30[8]! =
    expandTree 6 1792 fourRows30[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row09 : fourWide30[9]! =
    expandTree 6 1792 fourRows30[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row10 : fourWide30[10]! =
    expandTree 6 1792 fourRows30[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row11 : fourWide30[11]! =
    expandTree 6 1792 fourRows30[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row12 : fourWide30[12]! =
    expandTree 6 1792 fourRows30[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row13 : fourWide30[13]! =
    expandTree 6 1792 fourRows30[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row14 : fourWide30[14]! =
    expandTree 6 1792 fourRows30[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row15 : fourWide30[15]! =
    expandTree 6 1792 fourRows30[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row16 : fourWide30[16]! =
    expandTree 6 1792 fourRows30[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row17 : fourWide30[17]! =
    expandTree 6 1792 fourRows30[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row18 : fourWide30[18]! =
    expandTree 6 1792 fourRows30[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row19 : fourWide30[19]! =
    expandTree 6 1792 fourRows30[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row20 : fourWide30[20]! =
    expandTree 6 1792 fourRows30[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row21 : fourWide30[21]! =
    expandTree 6 1792 fourRows30[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row22 : fourWide30[22]! =
    expandTree 6 1792 fourRows30[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row23 : fourWide30[23]! =
    expandTree 6 1792 fourRows30[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row24 : fourWide30[24]! =
    expandTree 6 1792 fourRows30[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row25 : fourWide30[25]! =
    expandTree 6 1792 fourRows30[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row26 : fourWide30[26]! =
    expandTree 6 1792 fourRows30[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row27 : fourWide30[27]! =
    expandTree 6 1792 fourRows30[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row28 : fourWide30[28]! =
    expandTree 6 1792 fourRows30[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row29 : fourWide30[29]! =
    expandTree 6 1792 fourRows30[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row30 : fourWide30[30]! =
    expandTree 6 1792 fourRows30[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded30_row31 : fourWide30[31]! =
    expandTree 6 1792 fourRows30[31]! := by decide +kernel

private theorem expanded30 : fourWide30 =
    fourRows30.map (expandTree 6 1792) := by
  change [fourWide30[0]!,
    fourWide30[1]!,
    fourWide30[2]!,
    fourWide30[3]!,
    fourWide30[4]!,
    fourWide30[5]!,
    fourWide30[6]!,
    fourWide30[7]!,
    fourWide30[8]!,
    fourWide30[9]!,
    fourWide30[10]!,
    fourWide30[11]!,
    fourWide30[12]!,
    fourWide30[13]!,
    fourWide30[14]!,
    fourWide30[15]!,
    fourWide30[16]!,
    fourWide30[17]!,
    fourWide30[18]!,
    fourWide30[19]!,
    fourWide30[20]!,
    fourWide30[21]!,
    fourWide30[22]!,
    fourWide30[23]!,
    fourWide30[24]!,
    fourWide30[25]!,
    fourWide30[26]!,
    fourWide30[27]!,
    fourWide30[28]!,
    fourWide30[29]!,
    fourWide30[30]!,
    fourWide30[31]!] =
    [expandTree 6 1792 fourRows30[0]!,
     expandTree 6 1792 fourRows30[1]!,
     expandTree 6 1792 fourRows30[2]!,
     expandTree 6 1792 fourRows30[3]!,
     expandTree 6 1792 fourRows30[4]!,
     expandTree 6 1792 fourRows30[5]!,
     expandTree 6 1792 fourRows30[6]!,
     expandTree 6 1792 fourRows30[7]!,
     expandTree 6 1792 fourRows30[8]!,
     expandTree 6 1792 fourRows30[9]!,
     expandTree 6 1792 fourRows30[10]!,
     expandTree 6 1792 fourRows30[11]!,
     expandTree 6 1792 fourRows30[12]!,
     expandTree 6 1792 fourRows30[13]!,
     expandTree 6 1792 fourRows30[14]!,
     expandTree 6 1792 fourRows30[15]!,
     expandTree 6 1792 fourRows30[16]!,
     expandTree 6 1792 fourRows30[17]!,
     expandTree 6 1792 fourRows30[18]!,
     expandTree 6 1792 fourRows30[19]!,
     expandTree 6 1792 fourRows30[20]!,
     expandTree 6 1792 fourRows30[21]!,
     expandTree 6 1792 fourRows30[22]!,
     expandTree 6 1792 fourRows30[23]!,
     expandTree 6 1792 fourRows30[24]!,
     expandTree 6 1792 fourRows30[25]!,
     expandTree 6 1792 fourRows30[26]!,
     expandTree 6 1792 fourRows30[27]!,
     expandTree 6 1792 fourRows30[28]!,
     expandTree 6 1792 fourRows30[29]!,
     expandTree 6 1792 fourRows30[30]!,
     expandTree 6 1792 fourRows30[31]!]
  rw [expanded30_row00, expanded30_row01, expanded30_row02, expanded30_row03, expanded30_row04, expanded30_row05, expanded30_row06, expanded30_row07, expanded30_row08, expanded30_row09, expanded30_row10, expanded30_row11, expanded30_row12, expanded30_row13, expanded30_row14, expanded30_row15, expanded30_row16, expanded30_row17, expanded30_row18, expanded30_row19, expanded30_row20, expanded30_row21, expanded30_row22, expanded30_row23, expanded30_row24, expanded30_row25, expanded30_row26, expanded30_row27, expanded30_row28, expanded30_row29, expanded30_row30, expanded30_row31]

set_option maxRecDepth 8192 in
private theorem expanded31_row00 : fourWide31[0]! =
    expandTree 6 1792 fourRows31[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row01 : fourWide31[1]! =
    expandTree 6 1792 fourRows31[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row02 : fourWide31[2]! =
    expandTree 6 1792 fourRows31[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row03 : fourWide31[3]! =
    expandTree 6 1792 fourRows31[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row04 : fourWide31[4]! =
    expandTree 6 1792 fourRows31[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row05 : fourWide31[5]! =
    expandTree 6 1792 fourRows31[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row06 : fourWide31[6]! =
    expandTree 6 1792 fourRows31[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row07 : fourWide31[7]! =
    expandTree 6 1792 fourRows31[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row08 : fourWide31[8]! =
    expandTree 6 1792 fourRows31[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row09 : fourWide31[9]! =
    expandTree 6 1792 fourRows31[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row10 : fourWide31[10]! =
    expandTree 6 1792 fourRows31[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row11 : fourWide31[11]! =
    expandTree 6 1792 fourRows31[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row12 : fourWide31[12]! =
    expandTree 6 1792 fourRows31[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row13 : fourWide31[13]! =
    expandTree 6 1792 fourRows31[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row14 : fourWide31[14]! =
    expandTree 6 1792 fourRows31[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row15 : fourWide31[15]! =
    expandTree 6 1792 fourRows31[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row16 : fourWide31[16]! =
    expandTree 6 1792 fourRows31[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row17 : fourWide31[17]! =
    expandTree 6 1792 fourRows31[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row18 : fourWide31[18]! =
    expandTree 6 1792 fourRows31[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row19 : fourWide31[19]! =
    expandTree 6 1792 fourRows31[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row20 : fourWide31[20]! =
    expandTree 6 1792 fourRows31[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row21 : fourWide31[21]! =
    expandTree 6 1792 fourRows31[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row22 : fourWide31[22]! =
    expandTree 6 1792 fourRows31[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row23 : fourWide31[23]! =
    expandTree 6 1792 fourRows31[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row24 : fourWide31[24]! =
    expandTree 6 1792 fourRows31[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row25 : fourWide31[25]! =
    expandTree 6 1792 fourRows31[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row26 : fourWide31[26]! =
    expandTree 6 1792 fourRows31[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row27 : fourWide31[27]! =
    expandTree 6 1792 fourRows31[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row28 : fourWide31[28]! =
    expandTree 6 1792 fourRows31[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row29 : fourWide31[29]! =
    expandTree 6 1792 fourRows31[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row30 : fourWide31[30]! =
    expandTree 6 1792 fourRows31[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded31_row31 : fourWide31[31]! =
    expandTree 6 1792 fourRows31[31]! := by decide +kernel

private theorem expanded31 : fourWide31 =
    fourRows31.map (expandTree 6 1792) := by
  change [fourWide31[0]!,
    fourWide31[1]!,
    fourWide31[2]!,
    fourWide31[3]!,
    fourWide31[4]!,
    fourWide31[5]!,
    fourWide31[6]!,
    fourWide31[7]!,
    fourWide31[8]!,
    fourWide31[9]!,
    fourWide31[10]!,
    fourWide31[11]!,
    fourWide31[12]!,
    fourWide31[13]!,
    fourWide31[14]!,
    fourWide31[15]!,
    fourWide31[16]!,
    fourWide31[17]!,
    fourWide31[18]!,
    fourWide31[19]!,
    fourWide31[20]!,
    fourWide31[21]!,
    fourWide31[22]!,
    fourWide31[23]!,
    fourWide31[24]!,
    fourWide31[25]!,
    fourWide31[26]!,
    fourWide31[27]!,
    fourWide31[28]!,
    fourWide31[29]!,
    fourWide31[30]!,
    fourWide31[31]!] =
    [expandTree 6 1792 fourRows31[0]!,
     expandTree 6 1792 fourRows31[1]!,
     expandTree 6 1792 fourRows31[2]!,
     expandTree 6 1792 fourRows31[3]!,
     expandTree 6 1792 fourRows31[4]!,
     expandTree 6 1792 fourRows31[5]!,
     expandTree 6 1792 fourRows31[6]!,
     expandTree 6 1792 fourRows31[7]!,
     expandTree 6 1792 fourRows31[8]!,
     expandTree 6 1792 fourRows31[9]!,
     expandTree 6 1792 fourRows31[10]!,
     expandTree 6 1792 fourRows31[11]!,
     expandTree 6 1792 fourRows31[12]!,
     expandTree 6 1792 fourRows31[13]!,
     expandTree 6 1792 fourRows31[14]!,
     expandTree 6 1792 fourRows31[15]!,
     expandTree 6 1792 fourRows31[16]!,
     expandTree 6 1792 fourRows31[17]!,
     expandTree 6 1792 fourRows31[18]!,
     expandTree 6 1792 fourRows31[19]!,
     expandTree 6 1792 fourRows31[20]!,
     expandTree 6 1792 fourRows31[21]!,
     expandTree 6 1792 fourRows31[22]!,
     expandTree 6 1792 fourRows31[23]!,
     expandTree 6 1792 fourRows31[24]!,
     expandTree 6 1792 fourRows31[25]!,
     expandTree 6 1792 fourRows31[26]!,
     expandTree 6 1792 fourRows31[27]!,
     expandTree 6 1792 fourRows31[28]!,
     expandTree 6 1792 fourRows31[29]!,
     expandTree 6 1792 fourRows31[30]!,
     expandTree 6 1792 fourRows31[31]!]
  rw [expanded31_row00, expanded31_row01, expanded31_row02, expanded31_row03, expanded31_row04, expanded31_row05, expanded31_row06, expanded31_row07, expanded31_row08, expanded31_row09, expanded31_row10, expanded31_row11, expanded31_row12, expanded31_row13, expanded31_row14, expanded31_row15, expanded31_row16, expanded31_row17, expanded31_row18, expanded31_row19, expanded31_row20, expanded31_row21, expanded31_row22, expanded31_row23, expanded31_row24, expanded31_row25, expanded31_row26, expanded31_row27, expanded31_row28, expanded31_row29, expanded31_row30, expanded31_row31]

set_option maxRecDepth 8192 in
private theorem expanded32_row00 : fourWide32[0]! =
    expandTree 6 1792 fourRows32[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row01 : fourWide32[1]! =
    expandTree 6 1792 fourRows32[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row02 : fourWide32[2]! =
    expandTree 6 1792 fourRows32[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row03 : fourWide32[3]! =
    expandTree 6 1792 fourRows32[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row04 : fourWide32[4]! =
    expandTree 6 1792 fourRows32[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row05 : fourWide32[5]! =
    expandTree 6 1792 fourRows32[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row06 : fourWide32[6]! =
    expandTree 6 1792 fourRows32[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row07 : fourWide32[7]! =
    expandTree 6 1792 fourRows32[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row08 : fourWide32[8]! =
    expandTree 6 1792 fourRows32[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row09 : fourWide32[9]! =
    expandTree 6 1792 fourRows32[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row10 : fourWide32[10]! =
    expandTree 6 1792 fourRows32[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row11 : fourWide32[11]! =
    expandTree 6 1792 fourRows32[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row12 : fourWide32[12]! =
    expandTree 6 1792 fourRows32[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row13 : fourWide32[13]! =
    expandTree 6 1792 fourRows32[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row14 : fourWide32[14]! =
    expandTree 6 1792 fourRows32[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row15 : fourWide32[15]! =
    expandTree 6 1792 fourRows32[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row16 : fourWide32[16]! =
    expandTree 6 1792 fourRows32[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row17 : fourWide32[17]! =
    expandTree 6 1792 fourRows32[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row18 : fourWide32[18]! =
    expandTree 6 1792 fourRows32[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row19 : fourWide32[19]! =
    expandTree 6 1792 fourRows32[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row20 : fourWide32[20]! =
    expandTree 6 1792 fourRows32[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row21 : fourWide32[21]! =
    expandTree 6 1792 fourRows32[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row22 : fourWide32[22]! =
    expandTree 6 1792 fourRows32[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row23 : fourWide32[23]! =
    expandTree 6 1792 fourRows32[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row24 : fourWide32[24]! =
    expandTree 6 1792 fourRows32[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row25 : fourWide32[25]! =
    expandTree 6 1792 fourRows32[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row26 : fourWide32[26]! =
    expandTree 6 1792 fourRows32[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row27 : fourWide32[27]! =
    expandTree 6 1792 fourRows32[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row28 : fourWide32[28]! =
    expandTree 6 1792 fourRows32[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row29 : fourWide32[29]! =
    expandTree 6 1792 fourRows32[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row30 : fourWide32[30]! =
    expandTree 6 1792 fourRows32[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded32_row31 : fourWide32[31]! =
    expandTree 6 1792 fourRows32[31]! := by decide +kernel

private theorem expanded32 : fourWide32 =
    fourRows32.map (expandTree 6 1792) := by
  change [fourWide32[0]!,
    fourWide32[1]!,
    fourWide32[2]!,
    fourWide32[3]!,
    fourWide32[4]!,
    fourWide32[5]!,
    fourWide32[6]!,
    fourWide32[7]!,
    fourWide32[8]!,
    fourWide32[9]!,
    fourWide32[10]!,
    fourWide32[11]!,
    fourWide32[12]!,
    fourWide32[13]!,
    fourWide32[14]!,
    fourWide32[15]!,
    fourWide32[16]!,
    fourWide32[17]!,
    fourWide32[18]!,
    fourWide32[19]!,
    fourWide32[20]!,
    fourWide32[21]!,
    fourWide32[22]!,
    fourWide32[23]!,
    fourWide32[24]!,
    fourWide32[25]!,
    fourWide32[26]!,
    fourWide32[27]!,
    fourWide32[28]!,
    fourWide32[29]!,
    fourWide32[30]!,
    fourWide32[31]!] =
    [expandTree 6 1792 fourRows32[0]!,
     expandTree 6 1792 fourRows32[1]!,
     expandTree 6 1792 fourRows32[2]!,
     expandTree 6 1792 fourRows32[3]!,
     expandTree 6 1792 fourRows32[4]!,
     expandTree 6 1792 fourRows32[5]!,
     expandTree 6 1792 fourRows32[6]!,
     expandTree 6 1792 fourRows32[7]!,
     expandTree 6 1792 fourRows32[8]!,
     expandTree 6 1792 fourRows32[9]!,
     expandTree 6 1792 fourRows32[10]!,
     expandTree 6 1792 fourRows32[11]!,
     expandTree 6 1792 fourRows32[12]!,
     expandTree 6 1792 fourRows32[13]!,
     expandTree 6 1792 fourRows32[14]!,
     expandTree 6 1792 fourRows32[15]!,
     expandTree 6 1792 fourRows32[16]!,
     expandTree 6 1792 fourRows32[17]!,
     expandTree 6 1792 fourRows32[18]!,
     expandTree 6 1792 fourRows32[19]!,
     expandTree 6 1792 fourRows32[20]!,
     expandTree 6 1792 fourRows32[21]!,
     expandTree 6 1792 fourRows32[22]!,
     expandTree 6 1792 fourRows32[23]!,
     expandTree 6 1792 fourRows32[24]!,
     expandTree 6 1792 fourRows32[25]!,
     expandTree 6 1792 fourRows32[26]!,
     expandTree 6 1792 fourRows32[27]!,
     expandTree 6 1792 fourRows32[28]!,
     expandTree 6 1792 fourRows32[29]!,
     expandTree 6 1792 fourRows32[30]!,
     expandTree 6 1792 fourRows32[31]!]
  rw [expanded32_row00, expanded32_row01, expanded32_row02, expanded32_row03, expanded32_row04, expanded32_row05, expanded32_row06, expanded32_row07, expanded32_row08, expanded32_row09, expanded32_row10, expanded32_row11, expanded32_row12, expanded32_row13, expanded32_row14, expanded32_row15, expanded32_row16, expanded32_row17, expanded32_row18, expanded32_row19, expanded32_row20, expanded32_row21, expanded32_row22, expanded32_row23, expanded32_row24, expanded32_row25, expanded32_row26, expanded32_row27, expanded32_row28, expanded32_row29, expanded32_row30, expanded32_row31]

set_option maxRecDepth 8192 in
private theorem expanded33_row00 : fourWide33[0]! =
    expandTree 6 1792 fourRows33[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row01 : fourWide33[1]! =
    expandTree 6 1792 fourRows33[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row02 : fourWide33[2]! =
    expandTree 6 1792 fourRows33[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row03 : fourWide33[3]! =
    expandTree 6 1792 fourRows33[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row04 : fourWide33[4]! =
    expandTree 6 1792 fourRows33[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row05 : fourWide33[5]! =
    expandTree 6 1792 fourRows33[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row06 : fourWide33[6]! =
    expandTree 6 1792 fourRows33[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row07 : fourWide33[7]! =
    expandTree 6 1792 fourRows33[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row08 : fourWide33[8]! =
    expandTree 6 1792 fourRows33[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row09 : fourWide33[9]! =
    expandTree 6 1792 fourRows33[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row10 : fourWide33[10]! =
    expandTree 6 1792 fourRows33[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row11 : fourWide33[11]! =
    expandTree 6 1792 fourRows33[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row12 : fourWide33[12]! =
    expandTree 6 1792 fourRows33[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row13 : fourWide33[13]! =
    expandTree 6 1792 fourRows33[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row14 : fourWide33[14]! =
    expandTree 6 1792 fourRows33[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row15 : fourWide33[15]! =
    expandTree 6 1792 fourRows33[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row16 : fourWide33[16]! =
    expandTree 6 1792 fourRows33[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row17 : fourWide33[17]! =
    expandTree 6 1792 fourRows33[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row18 : fourWide33[18]! =
    expandTree 6 1792 fourRows33[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row19 : fourWide33[19]! =
    expandTree 6 1792 fourRows33[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row20 : fourWide33[20]! =
    expandTree 6 1792 fourRows33[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row21 : fourWide33[21]! =
    expandTree 6 1792 fourRows33[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row22 : fourWide33[22]! =
    expandTree 6 1792 fourRows33[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row23 : fourWide33[23]! =
    expandTree 6 1792 fourRows33[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row24 : fourWide33[24]! =
    expandTree 6 1792 fourRows33[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row25 : fourWide33[25]! =
    expandTree 6 1792 fourRows33[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row26 : fourWide33[26]! =
    expandTree 6 1792 fourRows33[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row27 : fourWide33[27]! =
    expandTree 6 1792 fourRows33[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row28 : fourWide33[28]! =
    expandTree 6 1792 fourRows33[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row29 : fourWide33[29]! =
    expandTree 6 1792 fourRows33[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row30 : fourWide33[30]! =
    expandTree 6 1792 fourRows33[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded33_row31 : fourWide33[31]! =
    expandTree 6 1792 fourRows33[31]! := by decide +kernel

private theorem expanded33 : fourWide33 =
    fourRows33.map (expandTree 6 1792) := by
  change [fourWide33[0]!,
    fourWide33[1]!,
    fourWide33[2]!,
    fourWide33[3]!,
    fourWide33[4]!,
    fourWide33[5]!,
    fourWide33[6]!,
    fourWide33[7]!,
    fourWide33[8]!,
    fourWide33[9]!,
    fourWide33[10]!,
    fourWide33[11]!,
    fourWide33[12]!,
    fourWide33[13]!,
    fourWide33[14]!,
    fourWide33[15]!,
    fourWide33[16]!,
    fourWide33[17]!,
    fourWide33[18]!,
    fourWide33[19]!,
    fourWide33[20]!,
    fourWide33[21]!,
    fourWide33[22]!,
    fourWide33[23]!,
    fourWide33[24]!,
    fourWide33[25]!,
    fourWide33[26]!,
    fourWide33[27]!,
    fourWide33[28]!,
    fourWide33[29]!,
    fourWide33[30]!,
    fourWide33[31]!] =
    [expandTree 6 1792 fourRows33[0]!,
     expandTree 6 1792 fourRows33[1]!,
     expandTree 6 1792 fourRows33[2]!,
     expandTree 6 1792 fourRows33[3]!,
     expandTree 6 1792 fourRows33[4]!,
     expandTree 6 1792 fourRows33[5]!,
     expandTree 6 1792 fourRows33[6]!,
     expandTree 6 1792 fourRows33[7]!,
     expandTree 6 1792 fourRows33[8]!,
     expandTree 6 1792 fourRows33[9]!,
     expandTree 6 1792 fourRows33[10]!,
     expandTree 6 1792 fourRows33[11]!,
     expandTree 6 1792 fourRows33[12]!,
     expandTree 6 1792 fourRows33[13]!,
     expandTree 6 1792 fourRows33[14]!,
     expandTree 6 1792 fourRows33[15]!,
     expandTree 6 1792 fourRows33[16]!,
     expandTree 6 1792 fourRows33[17]!,
     expandTree 6 1792 fourRows33[18]!,
     expandTree 6 1792 fourRows33[19]!,
     expandTree 6 1792 fourRows33[20]!,
     expandTree 6 1792 fourRows33[21]!,
     expandTree 6 1792 fourRows33[22]!,
     expandTree 6 1792 fourRows33[23]!,
     expandTree 6 1792 fourRows33[24]!,
     expandTree 6 1792 fourRows33[25]!,
     expandTree 6 1792 fourRows33[26]!,
     expandTree 6 1792 fourRows33[27]!,
     expandTree 6 1792 fourRows33[28]!,
     expandTree 6 1792 fourRows33[29]!,
     expandTree 6 1792 fourRows33[30]!,
     expandTree 6 1792 fourRows33[31]!]
  rw [expanded33_row00, expanded33_row01, expanded33_row02, expanded33_row03, expanded33_row04, expanded33_row05, expanded33_row06, expanded33_row07, expanded33_row08, expanded33_row09, expanded33_row10, expanded33_row11, expanded33_row12, expanded33_row13, expanded33_row14, expanded33_row15, expanded33_row16, expanded33_row17, expanded33_row18, expanded33_row19, expanded33_row20, expanded33_row21, expanded33_row22, expanded33_row23, expanded33_row24, expanded33_row25, expanded33_row26, expanded33_row27, expanded33_row28, expanded33_row29, expanded33_row30, expanded33_row31]

set_option maxRecDepth 8192 in
private theorem expanded34_row00 : fourWide34[0]! =
    expandTree 6 1792 fourRows34[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row01 : fourWide34[1]! =
    expandTree 6 1792 fourRows34[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row02 : fourWide34[2]! =
    expandTree 6 1792 fourRows34[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row03 : fourWide34[3]! =
    expandTree 6 1792 fourRows34[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row04 : fourWide34[4]! =
    expandTree 6 1792 fourRows34[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row05 : fourWide34[5]! =
    expandTree 6 1792 fourRows34[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row06 : fourWide34[6]! =
    expandTree 6 1792 fourRows34[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row07 : fourWide34[7]! =
    expandTree 6 1792 fourRows34[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row08 : fourWide34[8]! =
    expandTree 6 1792 fourRows34[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row09 : fourWide34[9]! =
    expandTree 6 1792 fourRows34[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row10 : fourWide34[10]! =
    expandTree 6 1792 fourRows34[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row11 : fourWide34[11]! =
    expandTree 6 1792 fourRows34[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row12 : fourWide34[12]! =
    expandTree 6 1792 fourRows34[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row13 : fourWide34[13]! =
    expandTree 6 1792 fourRows34[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row14 : fourWide34[14]! =
    expandTree 6 1792 fourRows34[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row15 : fourWide34[15]! =
    expandTree 6 1792 fourRows34[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row16 : fourWide34[16]! =
    expandTree 6 1792 fourRows34[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row17 : fourWide34[17]! =
    expandTree 6 1792 fourRows34[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row18 : fourWide34[18]! =
    expandTree 6 1792 fourRows34[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row19 : fourWide34[19]! =
    expandTree 6 1792 fourRows34[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row20 : fourWide34[20]! =
    expandTree 6 1792 fourRows34[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row21 : fourWide34[21]! =
    expandTree 6 1792 fourRows34[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row22 : fourWide34[22]! =
    expandTree 6 1792 fourRows34[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row23 : fourWide34[23]! =
    expandTree 6 1792 fourRows34[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row24 : fourWide34[24]! =
    expandTree 6 1792 fourRows34[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row25 : fourWide34[25]! =
    expandTree 6 1792 fourRows34[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row26 : fourWide34[26]! =
    expandTree 6 1792 fourRows34[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row27 : fourWide34[27]! =
    expandTree 6 1792 fourRows34[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row28 : fourWide34[28]! =
    expandTree 6 1792 fourRows34[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row29 : fourWide34[29]! =
    expandTree 6 1792 fourRows34[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row30 : fourWide34[30]! =
    expandTree 6 1792 fourRows34[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded34_row31 : fourWide34[31]! =
    expandTree 6 1792 fourRows34[31]! := by decide +kernel

private theorem expanded34 : fourWide34 =
    fourRows34.map (expandTree 6 1792) := by
  change [fourWide34[0]!,
    fourWide34[1]!,
    fourWide34[2]!,
    fourWide34[3]!,
    fourWide34[4]!,
    fourWide34[5]!,
    fourWide34[6]!,
    fourWide34[7]!,
    fourWide34[8]!,
    fourWide34[9]!,
    fourWide34[10]!,
    fourWide34[11]!,
    fourWide34[12]!,
    fourWide34[13]!,
    fourWide34[14]!,
    fourWide34[15]!,
    fourWide34[16]!,
    fourWide34[17]!,
    fourWide34[18]!,
    fourWide34[19]!,
    fourWide34[20]!,
    fourWide34[21]!,
    fourWide34[22]!,
    fourWide34[23]!,
    fourWide34[24]!,
    fourWide34[25]!,
    fourWide34[26]!,
    fourWide34[27]!,
    fourWide34[28]!,
    fourWide34[29]!,
    fourWide34[30]!,
    fourWide34[31]!] =
    [expandTree 6 1792 fourRows34[0]!,
     expandTree 6 1792 fourRows34[1]!,
     expandTree 6 1792 fourRows34[2]!,
     expandTree 6 1792 fourRows34[3]!,
     expandTree 6 1792 fourRows34[4]!,
     expandTree 6 1792 fourRows34[5]!,
     expandTree 6 1792 fourRows34[6]!,
     expandTree 6 1792 fourRows34[7]!,
     expandTree 6 1792 fourRows34[8]!,
     expandTree 6 1792 fourRows34[9]!,
     expandTree 6 1792 fourRows34[10]!,
     expandTree 6 1792 fourRows34[11]!,
     expandTree 6 1792 fourRows34[12]!,
     expandTree 6 1792 fourRows34[13]!,
     expandTree 6 1792 fourRows34[14]!,
     expandTree 6 1792 fourRows34[15]!,
     expandTree 6 1792 fourRows34[16]!,
     expandTree 6 1792 fourRows34[17]!,
     expandTree 6 1792 fourRows34[18]!,
     expandTree 6 1792 fourRows34[19]!,
     expandTree 6 1792 fourRows34[20]!,
     expandTree 6 1792 fourRows34[21]!,
     expandTree 6 1792 fourRows34[22]!,
     expandTree 6 1792 fourRows34[23]!,
     expandTree 6 1792 fourRows34[24]!,
     expandTree 6 1792 fourRows34[25]!,
     expandTree 6 1792 fourRows34[26]!,
     expandTree 6 1792 fourRows34[27]!,
     expandTree 6 1792 fourRows34[28]!,
     expandTree 6 1792 fourRows34[29]!,
     expandTree 6 1792 fourRows34[30]!,
     expandTree 6 1792 fourRows34[31]!]
  rw [expanded34_row00, expanded34_row01, expanded34_row02, expanded34_row03, expanded34_row04, expanded34_row05, expanded34_row06, expanded34_row07, expanded34_row08, expanded34_row09, expanded34_row10, expanded34_row11, expanded34_row12, expanded34_row13, expanded34_row14, expanded34_row15, expanded34_row16, expanded34_row17, expanded34_row18, expanded34_row19, expanded34_row20, expanded34_row21, expanded34_row22, expanded34_row23, expanded34_row24, expanded34_row25, expanded34_row26, expanded34_row27, expanded34_row28, expanded34_row29, expanded34_row30, expanded34_row31]

set_option maxRecDepth 8192 in
private theorem expanded35_row00 : fourWide35[0]! =
    expandTree 6 1792 fourRows35[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row01 : fourWide35[1]! =
    expandTree 6 1792 fourRows35[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row02 : fourWide35[2]! =
    expandTree 6 1792 fourRows35[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row03 : fourWide35[3]! =
    expandTree 6 1792 fourRows35[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row04 : fourWide35[4]! =
    expandTree 6 1792 fourRows35[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row05 : fourWide35[5]! =
    expandTree 6 1792 fourRows35[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row06 : fourWide35[6]! =
    expandTree 6 1792 fourRows35[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row07 : fourWide35[7]! =
    expandTree 6 1792 fourRows35[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row08 : fourWide35[8]! =
    expandTree 6 1792 fourRows35[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row09 : fourWide35[9]! =
    expandTree 6 1792 fourRows35[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row10 : fourWide35[10]! =
    expandTree 6 1792 fourRows35[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row11 : fourWide35[11]! =
    expandTree 6 1792 fourRows35[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row12 : fourWide35[12]! =
    expandTree 6 1792 fourRows35[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row13 : fourWide35[13]! =
    expandTree 6 1792 fourRows35[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row14 : fourWide35[14]! =
    expandTree 6 1792 fourRows35[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row15 : fourWide35[15]! =
    expandTree 6 1792 fourRows35[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row16 : fourWide35[16]! =
    expandTree 6 1792 fourRows35[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row17 : fourWide35[17]! =
    expandTree 6 1792 fourRows35[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row18 : fourWide35[18]! =
    expandTree 6 1792 fourRows35[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row19 : fourWide35[19]! =
    expandTree 6 1792 fourRows35[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row20 : fourWide35[20]! =
    expandTree 6 1792 fourRows35[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row21 : fourWide35[21]! =
    expandTree 6 1792 fourRows35[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row22 : fourWide35[22]! =
    expandTree 6 1792 fourRows35[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row23 : fourWide35[23]! =
    expandTree 6 1792 fourRows35[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row24 : fourWide35[24]! =
    expandTree 6 1792 fourRows35[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row25 : fourWide35[25]! =
    expandTree 6 1792 fourRows35[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row26 : fourWide35[26]! =
    expandTree 6 1792 fourRows35[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row27 : fourWide35[27]! =
    expandTree 6 1792 fourRows35[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row28 : fourWide35[28]! =
    expandTree 6 1792 fourRows35[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row29 : fourWide35[29]! =
    expandTree 6 1792 fourRows35[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row30 : fourWide35[30]! =
    expandTree 6 1792 fourRows35[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded35_row31 : fourWide35[31]! =
    expandTree 6 1792 fourRows35[31]! := by decide +kernel

private theorem expanded35 : fourWide35 =
    fourRows35.map (expandTree 6 1792) := by
  change [fourWide35[0]!,
    fourWide35[1]!,
    fourWide35[2]!,
    fourWide35[3]!,
    fourWide35[4]!,
    fourWide35[5]!,
    fourWide35[6]!,
    fourWide35[7]!,
    fourWide35[8]!,
    fourWide35[9]!,
    fourWide35[10]!,
    fourWide35[11]!,
    fourWide35[12]!,
    fourWide35[13]!,
    fourWide35[14]!,
    fourWide35[15]!,
    fourWide35[16]!,
    fourWide35[17]!,
    fourWide35[18]!,
    fourWide35[19]!,
    fourWide35[20]!,
    fourWide35[21]!,
    fourWide35[22]!,
    fourWide35[23]!,
    fourWide35[24]!,
    fourWide35[25]!,
    fourWide35[26]!,
    fourWide35[27]!,
    fourWide35[28]!,
    fourWide35[29]!,
    fourWide35[30]!,
    fourWide35[31]!] =
    [expandTree 6 1792 fourRows35[0]!,
     expandTree 6 1792 fourRows35[1]!,
     expandTree 6 1792 fourRows35[2]!,
     expandTree 6 1792 fourRows35[3]!,
     expandTree 6 1792 fourRows35[4]!,
     expandTree 6 1792 fourRows35[5]!,
     expandTree 6 1792 fourRows35[6]!,
     expandTree 6 1792 fourRows35[7]!,
     expandTree 6 1792 fourRows35[8]!,
     expandTree 6 1792 fourRows35[9]!,
     expandTree 6 1792 fourRows35[10]!,
     expandTree 6 1792 fourRows35[11]!,
     expandTree 6 1792 fourRows35[12]!,
     expandTree 6 1792 fourRows35[13]!,
     expandTree 6 1792 fourRows35[14]!,
     expandTree 6 1792 fourRows35[15]!,
     expandTree 6 1792 fourRows35[16]!,
     expandTree 6 1792 fourRows35[17]!,
     expandTree 6 1792 fourRows35[18]!,
     expandTree 6 1792 fourRows35[19]!,
     expandTree 6 1792 fourRows35[20]!,
     expandTree 6 1792 fourRows35[21]!,
     expandTree 6 1792 fourRows35[22]!,
     expandTree 6 1792 fourRows35[23]!,
     expandTree 6 1792 fourRows35[24]!,
     expandTree 6 1792 fourRows35[25]!,
     expandTree 6 1792 fourRows35[26]!,
     expandTree 6 1792 fourRows35[27]!,
     expandTree 6 1792 fourRows35[28]!,
     expandTree 6 1792 fourRows35[29]!,
     expandTree 6 1792 fourRows35[30]!,
     expandTree 6 1792 fourRows35[31]!]
  rw [expanded35_row00, expanded35_row01, expanded35_row02, expanded35_row03, expanded35_row04, expanded35_row05, expanded35_row06, expanded35_row07, expanded35_row08, expanded35_row09, expanded35_row10, expanded35_row11, expanded35_row12, expanded35_row13, expanded35_row14, expanded35_row15, expanded35_row16, expanded35_row17, expanded35_row18, expanded35_row19, expanded35_row20, expanded35_row21, expanded35_row22, expanded35_row23, expanded35_row24, expanded35_row25, expanded35_row26, expanded35_row27, expanded35_row28, expanded35_row29, expanded35_row30, expanded35_row31]

set_option maxRecDepth 8192 in
private theorem expanded36_row00 : fourWide36[0]! =
    expandTree 6 1792 fourRows36[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row01 : fourWide36[1]! =
    expandTree 6 1792 fourRows36[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row02 : fourWide36[2]! =
    expandTree 6 1792 fourRows36[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row03 : fourWide36[3]! =
    expandTree 6 1792 fourRows36[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row04 : fourWide36[4]! =
    expandTree 6 1792 fourRows36[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row05 : fourWide36[5]! =
    expandTree 6 1792 fourRows36[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row06 : fourWide36[6]! =
    expandTree 6 1792 fourRows36[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row07 : fourWide36[7]! =
    expandTree 6 1792 fourRows36[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row08 : fourWide36[8]! =
    expandTree 6 1792 fourRows36[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row09 : fourWide36[9]! =
    expandTree 6 1792 fourRows36[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row10 : fourWide36[10]! =
    expandTree 6 1792 fourRows36[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row11 : fourWide36[11]! =
    expandTree 6 1792 fourRows36[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row12 : fourWide36[12]! =
    expandTree 6 1792 fourRows36[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row13 : fourWide36[13]! =
    expandTree 6 1792 fourRows36[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row14 : fourWide36[14]! =
    expandTree 6 1792 fourRows36[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row15 : fourWide36[15]! =
    expandTree 6 1792 fourRows36[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row16 : fourWide36[16]! =
    expandTree 6 1792 fourRows36[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row17 : fourWide36[17]! =
    expandTree 6 1792 fourRows36[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row18 : fourWide36[18]! =
    expandTree 6 1792 fourRows36[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row19 : fourWide36[19]! =
    expandTree 6 1792 fourRows36[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row20 : fourWide36[20]! =
    expandTree 6 1792 fourRows36[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row21 : fourWide36[21]! =
    expandTree 6 1792 fourRows36[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row22 : fourWide36[22]! =
    expandTree 6 1792 fourRows36[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row23 : fourWide36[23]! =
    expandTree 6 1792 fourRows36[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row24 : fourWide36[24]! =
    expandTree 6 1792 fourRows36[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row25 : fourWide36[25]! =
    expandTree 6 1792 fourRows36[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row26 : fourWide36[26]! =
    expandTree 6 1792 fourRows36[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row27 : fourWide36[27]! =
    expandTree 6 1792 fourRows36[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row28 : fourWide36[28]! =
    expandTree 6 1792 fourRows36[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row29 : fourWide36[29]! =
    expandTree 6 1792 fourRows36[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row30 : fourWide36[30]! =
    expandTree 6 1792 fourRows36[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded36_row31 : fourWide36[31]! =
    expandTree 6 1792 fourRows36[31]! := by decide +kernel

private theorem expanded36 : fourWide36 =
    fourRows36.map (expandTree 6 1792) := by
  change [fourWide36[0]!,
    fourWide36[1]!,
    fourWide36[2]!,
    fourWide36[3]!,
    fourWide36[4]!,
    fourWide36[5]!,
    fourWide36[6]!,
    fourWide36[7]!,
    fourWide36[8]!,
    fourWide36[9]!,
    fourWide36[10]!,
    fourWide36[11]!,
    fourWide36[12]!,
    fourWide36[13]!,
    fourWide36[14]!,
    fourWide36[15]!,
    fourWide36[16]!,
    fourWide36[17]!,
    fourWide36[18]!,
    fourWide36[19]!,
    fourWide36[20]!,
    fourWide36[21]!,
    fourWide36[22]!,
    fourWide36[23]!,
    fourWide36[24]!,
    fourWide36[25]!,
    fourWide36[26]!,
    fourWide36[27]!,
    fourWide36[28]!,
    fourWide36[29]!,
    fourWide36[30]!,
    fourWide36[31]!] =
    [expandTree 6 1792 fourRows36[0]!,
     expandTree 6 1792 fourRows36[1]!,
     expandTree 6 1792 fourRows36[2]!,
     expandTree 6 1792 fourRows36[3]!,
     expandTree 6 1792 fourRows36[4]!,
     expandTree 6 1792 fourRows36[5]!,
     expandTree 6 1792 fourRows36[6]!,
     expandTree 6 1792 fourRows36[7]!,
     expandTree 6 1792 fourRows36[8]!,
     expandTree 6 1792 fourRows36[9]!,
     expandTree 6 1792 fourRows36[10]!,
     expandTree 6 1792 fourRows36[11]!,
     expandTree 6 1792 fourRows36[12]!,
     expandTree 6 1792 fourRows36[13]!,
     expandTree 6 1792 fourRows36[14]!,
     expandTree 6 1792 fourRows36[15]!,
     expandTree 6 1792 fourRows36[16]!,
     expandTree 6 1792 fourRows36[17]!,
     expandTree 6 1792 fourRows36[18]!,
     expandTree 6 1792 fourRows36[19]!,
     expandTree 6 1792 fourRows36[20]!,
     expandTree 6 1792 fourRows36[21]!,
     expandTree 6 1792 fourRows36[22]!,
     expandTree 6 1792 fourRows36[23]!,
     expandTree 6 1792 fourRows36[24]!,
     expandTree 6 1792 fourRows36[25]!,
     expandTree 6 1792 fourRows36[26]!,
     expandTree 6 1792 fourRows36[27]!,
     expandTree 6 1792 fourRows36[28]!,
     expandTree 6 1792 fourRows36[29]!,
     expandTree 6 1792 fourRows36[30]!,
     expandTree 6 1792 fourRows36[31]!]
  rw [expanded36_row00, expanded36_row01, expanded36_row02, expanded36_row03, expanded36_row04, expanded36_row05, expanded36_row06, expanded36_row07, expanded36_row08, expanded36_row09, expanded36_row10, expanded36_row11, expanded36_row12, expanded36_row13, expanded36_row14, expanded36_row15, expanded36_row16, expanded36_row17, expanded36_row18, expanded36_row19, expanded36_row20, expanded36_row21, expanded36_row22, expanded36_row23, expanded36_row24, expanded36_row25, expanded36_row26, expanded36_row27, expanded36_row28, expanded36_row29, expanded36_row30, expanded36_row31]

set_option maxRecDepth 8192 in
private theorem expanded37_row00 : fourWide37[0]! =
    expandTree 6 1792 fourRows37[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row01 : fourWide37[1]! =
    expandTree 6 1792 fourRows37[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row02 : fourWide37[2]! =
    expandTree 6 1792 fourRows37[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row03 : fourWide37[3]! =
    expandTree 6 1792 fourRows37[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row04 : fourWide37[4]! =
    expandTree 6 1792 fourRows37[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row05 : fourWide37[5]! =
    expandTree 6 1792 fourRows37[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row06 : fourWide37[6]! =
    expandTree 6 1792 fourRows37[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row07 : fourWide37[7]! =
    expandTree 6 1792 fourRows37[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row08 : fourWide37[8]! =
    expandTree 6 1792 fourRows37[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row09 : fourWide37[9]! =
    expandTree 6 1792 fourRows37[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row10 : fourWide37[10]! =
    expandTree 6 1792 fourRows37[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row11 : fourWide37[11]! =
    expandTree 6 1792 fourRows37[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row12 : fourWide37[12]! =
    expandTree 6 1792 fourRows37[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row13 : fourWide37[13]! =
    expandTree 6 1792 fourRows37[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row14 : fourWide37[14]! =
    expandTree 6 1792 fourRows37[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row15 : fourWide37[15]! =
    expandTree 6 1792 fourRows37[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row16 : fourWide37[16]! =
    expandTree 6 1792 fourRows37[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row17 : fourWide37[17]! =
    expandTree 6 1792 fourRows37[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row18 : fourWide37[18]! =
    expandTree 6 1792 fourRows37[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row19 : fourWide37[19]! =
    expandTree 6 1792 fourRows37[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row20 : fourWide37[20]! =
    expandTree 6 1792 fourRows37[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row21 : fourWide37[21]! =
    expandTree 6 1792 fourRows37[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row22 : fourWide37[22]! =
    expandTree 6 1792 fourRows37[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row23 : fourWide37[23]! =
    expandTree 6 1792 fourRows37[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row24 : fourWide37[24]! =
    expandTree 6 1792 fourRows37[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row25 : fourWide37[25]! =
    expandTree 6 1792 fourRows37[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row26 : fourWide37[26]! =
    expandTree 6 1792 fourRows37[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row27 : fourWide37[27]! =
    expandTree 6 1792 fourRows37[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row28 : fourWide37[28]! =
    expandTree 6 1792 fourRows37[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row29 : fourWide37[29]! =
    expandTree 6 1792 fourRows37[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row30 : fourWide37[30]! =
    expandTree 6 1792 fourRows37[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded37_row31 : fourWide37[31]! =
    expandTree 6 1792 fourRows37[31]! := by decide +kernel

private theorem expanded37 : fourWide37 =
    fourRows37.map (expandTree 6 1792) := by
  change [fourWide37[0]!,
    fourWide37[1]!,
    fourWide37[2]!,
    fourWide37[3]!,
    fourWide37[4]!,
    fourWide37[5]!,
    fourWide37[6]!,
    fourWide37[7]!,
    fourWide37[8]!,
    fourWide37[9]!,
    fourWide37[10]!,
    fourWide37[11]!,
    fourWide37[12]!,
    fourWide37[13]!,
    fourWide37[14]!,
    fourWide37[15]!,
    fourWide37[16]!,
    fourWide37[17]!,
    fourWide37[18]!,
    fourWide37[19]!,
    fourWide37[20]!,
    fourWide37[21]!,
    fourWide37[22]!,
    fourWide37[23]!,
    fourWide37[24]!,
    fourWide37[25]!,
    fourWide37[26]!,
    fourWide37[27]!,
    fourWide37[28]!,
    fourWide37[29]!,
    fourWide37[30]!,
    fourWide37[31]!] =
    [expandTree 6 1792 fourRows37[0]!,
     expandTree 6 1792 fourRows37[1]!,
     expandTree 6 1792 fourRows37[2]!,
     expandTree 6 1792 fourRows37[3]!,
     expandTree 6 1792 fourRows37[4]!,
     expandTree 6 1792 fourRows37[5]!,
     expandTree 6 1792 fourRows37[6]!,
     expandTree 6 1792 fourRows37[7]!,
     expandTree 6 1792 fourRows37[8]!,
     expandTree 6 1792 fourRows37[9]!,
     expandTree 6 1792 fourRows37[10]!,
     expandTree 6 1792 fourRows37[11]!,
     expandTree 6 1792 fourRows37[12]!,
     expandTree 6 1792 fourRows37[13]!,
     expandTree 6 1792 fourRows37[14]!,
     expandTree 6 1792 fourRows37[15]!,
     expandTree 6 1792 fourRows37[16]!,
     expandTree 6 1792 fourRows37[17]!,
     expandTree 6 1792 fourRows37[18]!,
     expandTree 6 1792 fourRows37[19]!,
     expandTree 6 1792 fourRows37[20]!,
     expandTree 6 1792 fourRows37[21]!,
     expandTree 6 1792 fourRows37[22]!,
     expandTree 6 1792 fourRows37[23]!,
     expandTree 6 1792 fourRows37[24]!,
     expandTree 6 1792 fourRows37[25]!,
     expandTree 6 1792 fourRows37[26]!,
     expandTree 6 1792 fourRows37[27]!,
     expandTree 6 1792 fourRows37[28]!,
     expandTree 6 1792 fourRows37[29]!,
     expandTree 6 1792 fourRows37[30]!,
     expandTree 6 1792 fourRows37[31]!]
  rw [expanded37_row00, expanded37_row01, expanded37_row02, expanded37_row03, expanded37_row04, expanded37_row05, expanded37_row06, expanded37_row07, expanded37_row08, expanded37_row09, expanded37_row10, expanded37_row11, expanded37_row12, expanded37_row13, expanded37_row14, expanded37_row15, expanded37_row16, expanded37_row17, expanded37_row18, expanded37_row19, expanded37_row20, expanded37_row21, expanded37_row22, expanded37_row23, expanded37_row24, expanded37_row25, expanded37_row26, expanded37_row27, expanded37_row28, expanded37_row29, expanded37_row30, expanded37_row31]

set_option maxRecDepth 8192 in
private theorem expanded38_row00 : fourWide38[0]! =
    expandTree 6 1792 fourRows38[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row01 : fourWide38[1]! =
    expandTree 6 1792 fourRows38[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row02 : fourWide38[2]! =
    expandTree 6 1792 fourRows38[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row03 : fourWide38[3]! =
    expandTree 6 1792 fourRows38[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row04 : fourWide38[4]! =
    expandTree 6 1792 fourRows38[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row05 : fourWide38[5]! =
    expandTree 6 1792 fourRows38[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row06 : fourWide38[6]! =
    expandTree 6 1792 fourRows38[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row07 : fourWide38[7]! =
    expandTree 6 1792 fourRows38[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row08 : fourWide38[8]! =
    expandTree 6 1792 fourRows38[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row09 : fourWide38[9]! =
    expandTree 6 1792 fourRows38[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row10 : fourWide38[10]! =
    expandTree 6 1792 fourRows38[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row11 : fourWide38[11]! =
    expandTree 6 1792 fourRows38[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row12 : fourWide38[12]! =
    expandTree 6 1792 fourRows38[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row13 : fourWide38[13]! =
    expandTree 6 1792 fourRows38[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row14 : fourWide38[14]! =
    expandTree 6 1792 fourRows38[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row15 : fourWide38[15]! =
    expandTree 6 1792 fourRows38[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row16 : fourWide38[16]! =
    expandTree 6 1792 fourRows38[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row17 : fourWide38[17]! =
    expandTree 6 1792 fourRows38[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row18 : fourWide38[18]! =
    expandTree 6 1792 fourRows38[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row19 : fourWide38[19]! =
    expandTree 6 1792 fourRows38[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row20 : fourWide38[20]! =
    expandTree 6 1792 fourRows38[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row21 : fourWide38[21]! =
    expandTree 6 1792 fourRows38[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row22 : fourWide38[22]! =
    expandTree 6 1792 fourRows38[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row23 : fourWide38[23]! =
    expandTree 6 1792 fourRows38[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row24 : fourWide38[24]! =
    expandTree 6 1792 fourRows38[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row25 : fourWide38[25]! =
    expandTree 6 1792 fourRows38[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row26 : fourWide38[26]! =
    expandTree 6 1792 fourRows38[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row27 : fourWide38[27]! =
    expandTree 6 1792 fourRows38[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row28 : fourWide38[28]! =
    expandTree 6 1792 fourRows38[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row29 : fourWide38[29]! =
    expandTree 6 1792 fourRows38[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row30 : fourWide38[30]! =
    expandTree 6 1792 fourRows38[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded38_row31 : fourWide38[31]! =
    expandTree 6 1792 fourRows38[31]! := by decide +kernel

private theorem expanded38 : fourWide38 =
    fourRows38.map (expandTree 6 1792) := by
  change [fourWide38[0]!,
    fourWide38[1]!,
    fourWide38[2]!,
    fourWide38[3]!,
    fourWide38[4]!,
    fourWide38[5]!,
    fourWide38[6]!,
    fourWide38[7]!,
    fourWide38[8]!,
    fourWide38[9]!,
    fourWide38[10]!,
    fourWide38[11]!,
    fourWide38[12]!,
    fourWide38[13]!,
    fourWide38[14]!,
    fourWide38[15]!,
    fourWide38[16]!,
    fourWide38[17]!,
    fourWide38[18]!,
    fourWide38[19]!,
    fourWide38[20]!,
    fourWide38[21]!,
    fourWide38[22]!,
    fourWide38[23]!,
    fourWide38[24]!,
    fourWide38[25]!,
    fourWide38[26]!,
    fourWide38[27]!,
    fourWide38[28]!,
    fourWide38[29]!,
    fourWide38[30]!,
    fourWide38[31]!] =
    [expandTree 6 1792 fourRows38[0]!,
     expandTree 6 1792 fourRows38[1]!,
     expandTree 6 1792 fourRows38[2]!,
     expandTree 6 1792 fourRows38[3]!,
     expandTree 6 1792 fourRows38[4]!,
     expandTree 6 1792 fourRows38[5]!,
     expandTree 6 1792 fourRows38[6]!,
     expandTree 6 1792 fourRows38[7]!,
     expandTree 6 1792 fourRows38[8]!,
     expandTree 6 1792 fourRows38[9]!,
     expandTree 6 1792 fourRows38[10]!,
     expandTree 6 1792 fourRows38[11]!,
     expandTree 6 1792 fourRows38[12]!,
     expandTree 6 1792 fourRows38[13]!,
     expandTree 6 1792 fourRows38[14]!,
     expandTree 6 1792 fourRows38[15]!,
     expandTree 6 1792 fourRows38[16]!,
     expandTree 6 1792 fourRows38[17]!,
     expandTree 6 1792 fourRows38[18]!,
     expandTree 6 1792 fourRows38[19]!,
     expandTree 6 1792 fourRows38[20]!,
     expandTree 6 1792 fourRows38[21]!,
     expandTree 6 1792 fourRows38[22]!,
     expandTree 6 1792 fourRows38[23]!,
     expandTree 6 1792 fourRows38[24]!,
     expandTree 6 1792 fourRows38[25]!,
     expandTree 6 1792 fourRows38[26]!,
     expandTree 6 1792 fourRows38[27]!,
     expandTree 6 1792 fourRows38[28]!,
     expandTree 6 1792 fourRows38[29]!,
     expandTree 6 1792 fourRows38[30]!,
     expandTree 6 1792 fourRows38[31]!]
  rw [expanded38_row00, expanded38_row01, expanded38_row02, expanded38_row03, expanded38_row04, expanded38_row05, expanded38_row06, expanded38_row07, expanded38_row08, expanded38_row09, expanded38_row10, expanded38_row11, expanded38_row12, expanded38_row13, expanded38_row14, expanded38_row15, expanded38_row16, expanded38_row17, expanded38_row18, expanded38_row19, expanded38_row20, expanded38_row21, expanded38_row22, expanded38_row23, expanded38_row24, expanded38_row25, expanded38_row26, expanded38_row27, expanded38_row28, expanded38_row29, expanded38_row30, expanded38_row31]

set_option maxRecDepth 8192 in
private theorem expanded39_row00 : fourWide39[0]! =
    expandTree 6 1792 fourRows39[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row01 : fourWide39[1]! =
    expandTree 6 1792 fourRows39[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row02 : fourWide39[2]! =
    expandTree 6 1792 fourRows39[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row03 : fourWide39[3]! =
    expandTree 6 1792 fourRows39[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row04 : fourWide39[4]! =
    expandTree 6 1792 fourRows39[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row05 : fourWide39[5]! =
    expandTree 6 1792 fourRows39[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row06 : fourWide39[6]! =
    expandTree 6 1792 fourRows39[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row07 : fourWide39[7]! =
    expandTree 6 1792 fourRows39[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row08 : fourWide39[8]! =
    expandTree 6 1792 fourRows39[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row09 : fourWide39[9]! =
    expandTree 6 1792 fourRows39[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row10 : fourWide39[10]! =
    expandTree 6 1792 fourRows39[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row11 : fourWide39[11]! =
    expandTree 6 1792 fourRows39[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row12 : fourWide39[12]! =
    expandTree 6 1792 fourRows39[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row13 : fourWide39[13]! =
    expandTree 6 1792 fourRows39[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row14 : fourWide39[14]! =
    expandTree 6 1792 fourRows39[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row15 : fourWide39[15]! =
    expandTree 6 1792 fourRows39[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row16 : fourWide39[16]! =
    expandTree 6 1792 fourRows39[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row17 : fourWide39[17]! =
    expandTree 6 1792 fourRows39[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row18 : fourWide39[18]! =
    expandTree 6 1792 fourRows39[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row19 : fourWide39[19]! =
    expandTree 6 1792 fourRows39[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row20 : fourWide39[20]! =
    expandTree 6 1792 fourRows39[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row21 : fourWide39[21]! =
    expandTree 6 1792 fourRows39[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row22 : fourWide39[22]! =
    expandTree 6 1792 fourRows39[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row23 : fourWide39[23]! =
    expandTree 6 1792 fourRows39[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row24 : fourWide39[24]! =
    expandTree 6 1792 fourRows39[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row25 : fourWide39[25]! =
    expandTree 6 1792 fourRows39[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row26 : fourWide39[26]! =
    expandTree 6 1792 fourRows39[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row27 : fourWide39[27]! =
    expandTree 6 1792 fourRows39[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row28 : fourWide39[28]! =
    expandTree 6 1792 fourRows39[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row29 : fourWide39[29]! =
    expandTree 6 1792 fourRows39[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row30 : fourWide39[30]! =
    expandTree 6 1792 fourRows39[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded39_row31 : fourWide39[31]! =
    expandTree 6 1792 fourRows39[31]! := by decide +kernel

private theorem expanded39 : fourWide39 =
    fourRows39.map (expandTree 6 1792) := by
  change [fourWide39[0]!,
    fourWide39[1]!,
    fourWide39[2]!,
    fourWide39[3]!,
    fourWide39[4]!,
    fourWide39[5]!,
    fourWide39[6]!,
    fourWide39[7]!,
    fourWide39[8]!,
    fourWide39[9]!,
    fourWide39[10]!,
    fourWide39[11]!,
    fourWide39[12]!,
    fourWide39[13]!,
    fourWide39[14]!,
    fourWide39[15]!,
    fourWide39[16]!,
    fourWide39[17]!,
    fourWide39[18]!,
    fourWide39[19]!,
    fourWide39[20]!,
    fourWide39[21]!,
    fourWide39[22]!,
    fourWide39[23]!,
    fourWide39[24]!,
    fourWide39[25]!,
    fourWide39[26]!,
    fourWide39[27]!,
    fourWide39[28]!,
    fourWide39[29]!,
    fourWide39[30]!,
    fourWide39[31]!] =
    [expandTree 6 1792 fourRows39[0]!,
     expandTree 6 1792 fourRows39[1]!,
     expandTree 6 1792 fourRows39[2]!,
     expandTree 6 1792 fourRows39[3]!,
     expandTree 6 1792 fourRows39[4]!,
     expandTree 6 1792 fourRows39[5]!,
     expandTree 6 1792 fourRows39[6]!,
     expandTree 6 1792 fourRows39[7]!,
     expandTree 6 1792 fourRows39[8]!,
     expandTree 6 1792 fourRows39[9]!,
     expandTree 6 1792 fourRows39[10]!,
     expandTree 6 1792 fourRows39[11]!,
     expandTree 6 1792 fourRows39[12]!,
     expandTree 6 1792 fourRows39[13]!,
     expandTree 6 1792 fourRows39[14]!,
     expandTree 6 1792 fourRows39[15]!,
     expandTree 6 1792 fourRows39[16]!,
     expandTree 6 1792 fourRows39[17]!,
     expandTree 6 1792 fourRows39[18]!,
     expandTree 6 1792 fourRows39[19]!,
     expandTree 6 1792 fourRows39[20]!,
     expandTree 6 1792 fourRows39[21]!,
     expandTree 6 1792 fourRows39[22]!,
     expandTree 6 1792 fourRows39[23]!,
     expandTree 6 1792 fourRows39[24]!,
     expandTree 6 1792 fourRows39[25]!,
     expandTree 6 1792 fourRows39[26]!,
     expandTree 6 1792 fourRows39[27]!,
     expandTree 6 1792 fourRows39[28]!,
     expandTree 6 1792 fourRows39[29]!,
     expandTree 6 1792 fourRows39[30]!,
     expandTree 6 1792 fourRows39[31]!]
  rw [expanded39_row00, expanded39_row01, expanded39_row02, expanded39_row03, expanded39_row04, expanded39_row05, expanded39_row06, expanded39_row07, expanded39_row08, expanded39_row09, expanded39_row10, expanded39_row11, expanded39_row12, expanded39_row13, expanded39_row14, expanded39_row15, expanded39_row16, expanded39_row17, expanded39_row18, expanded39_row19, expanded39_row20, expanded39_row21, expanded39_row22, expanded39_row23, expanded39_row24, expanded39_row25, expanded39_row26, expanded39_row27, expanded39_row28, expanded39_row29, expanded39_row30, expanded39_row31]

set_option maxRecDepth 8192 in
private theorem expanded40_row00 : fourWide40[0]! =
    expandTree 6 1792 fourRows40[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row01 : fourWide40[1]! =
    expandTree 6 1792 fourRows40[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row02 : fourWide40[2]! =
    expandTree 6 1792 fourRows40[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row03 : fourWide40[3]! =
    expandTree 6 1792 fourRows40[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row04 : fourWide40[4]! =
    expandTree 6 1792 fourRows40[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row05 : fourWide40[5]! =
    expandTree 6 1792 fourRows40[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row06 : fourWide40[6]! =
    expandTree 6 1792 fourRows40[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row07 : fourWide40[7]! =
    expandTree 6 1792 fourRows40[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row08 : fourWide40[8]! =
    expandTree 6 1792 fourRows40[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row09 : fourWide40[9]! =
    expandTree 6 1792 fourRows40[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row10 : fourWide40[10]! =
    expandTree 6 1792 fourRows40[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row11 : fourWide40[11]! =
    expandTree 6 1792 fourRows40[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row12 : fourWide40[12]! =
    expandTree 6 1792 fourRows40[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row13 : fourWide40[13]! =
    expandTree 6 1792 fourRows40[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row14 : fourWide40[14]! =
    expandTree 6 1792 fourRows40[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row15 : fourWide40[15]! =
    expandTree 6 1792 fourRows40[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row16 : fourWide40[16]! =
    expandTree 6 1792 fourRows40[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row17 : fourWide40[17]! =
    expandTree 6 1792 fourRows40[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row18 : fourWide40[18]! =
    expandTree 6 1792 fourRows40[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row19 : fourWide40[19]! =
    expandTree 6 1792 fourRows40[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row20 : fourWide40[20]! =
    expandTree 6 1792 fourRows40[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row21 : fourWide40[21]! =
    expandTree 6 1792 fourRows40[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row22 : fourWide40[22]! =
    expandTree 6 1792 fourRows40[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row23 : fourWide40[23]! =
    expandTree 6 1792 fourRows40[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row24 : fourWide40[24]! =
    expandTree 6 1792 fourRows40[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row25 : fourWide40[25]! =
    expandTree 6 1792 fourRows40[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row26 : fourWide40[26]! =
    expandTree 6 1792 fourRows40[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row27 : fourWide40[27]! =
    expandTree 6 1792 fourRows40[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row28 : fourWide40[28]! =
    expandTree 6 1792 fourRows40[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row29 : fourWide40[29]! =
    expandTree 6 1792 fourRows40[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row30 : fourWide40[30]! =
    expandTree 6 1792 fourRows40[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded40_row31 : fourWide40[31]! =
    expandTree 6 1792 fourRows40[31]! := by decide +kernel

private theorem expanded40 : fourWide40 =
    fourRows40.map (expandTree 6 1792) := by
  change [fourWide40[0]!,
    fourWide40[1]!,
    fourWide40[2]!,
    fourWide40[3]!,
    fourWide40[4]!,
    fourWide40[5]!,
    fourWide40[6]!,
    fourWide40[7]!,
    fourWide40[8]!,
    fourWide40[9]!,
    fourWide40[10]!,
    fourWide40[11]!,
    fourWide40[12]!,
    fourWide40[13]!,
    fourWide40[14]!,
    fourWide40[15]!,
    fourWide40[16]!,
    fourWide40[17]!,
    fourWide40[18]!,
    fourWide40[19]!,
    fourWide40[20]!,
    fourWide40[21]!,
    fourWide40[22]!,
    fourWide40[23]!,
    fourWide40[24]!,
    fourWide40[25]!,
    fourWide40[26]!,
    fourWide40[27]!,
    fourWide40[28]!,
    fourWide40[29]!,
    fourWide40[30]!,
    fourWide40[31]!] =
    [expandTree 6 1792 fourRows40[0]!,
     expandTree 6 1792 fourRows40[1]!,
     expandTree 6 1792 fourRows40[2]!,
     expandTree 6 1792 fourRows40[3]!,
     expandTree 6 1792 fourRows40[4]!,
     expandTree 6 1792 fourRows40[5]!,
     expandTree 6 1792 fourRows40[6]!,
     expandTree 6 1792 fourRows40[7]!,
     expandTree 6 1792 fourRows40[8]!,
     expandTree 6 1792 fourRows40[9]!,
     expandTree 6 1792 fourRows40[10]!,
     expandTree 6 1792 fourRows40[11]!,
     expandTree 6 1792 fourRows40[12]!,
     expandTree 6 1792 fourRows40[13]!,
     expandTree 6 1792 fourRows40[14]!,
     expandTree 6 1792 fourRows40[15]!,
     expandTree 6 1792 fourRows40[16]!,
     expandTree 6 1792 fourRows40[17]!,
     expandTree 6 1792 fourRows40[18]!,
     expandTree 6 1792 fourRows40[19]!,
     expandTree 6 1792 fourRows40[20]!,
     expandTree 6 1792 fourRows40[21]!,
     expandTree 6 1792 fourRows40[22]!,
     expandTree 6 1792 fourRows40[23]!,
     expandTree 6 1792 fourRows40[24]!,
     expandTree 6 1792 fourRows40[25]!,
     expandTree 6 1792 fourRows40[26]!,
     expandTree 6 1792 fourRows40[27]!,
     expandTree 6 1792 fourRows40[28]!,
     expandTree 6 1792 fourRows40[29]!,
     expandTree 6 1792 fourRows40[30]!,
     expandTree 6 1792 fourRows40[31]!]
  rw [expanded40_row00, expanded40_row01, expanded40_row02, expanded40_row03, expanded40_row04, expanded40_row05, expanded40_row06, expanded40_row07, expanded40_row08, expanded40_row09, expanded40_row10, expanded40_row11, expanded40_row12, expanded40_row13, expanded40_row14, expanded40_row15, expanded40_row16, expanded40_row17, expanded40_row18, expanded40_row19, expanded40_row20, expanded40_row21, expanded40_row22, expanded40_row23, expanded40_row24, expanded40_row25, expanded40_row26, expanded40_row27, expanded40_row28, expanded40_row29, expanded40_row30, expanded40_row31]

set_option maxRecDepth 8192 in
private theorem expanded41_row00 : fourWide41[0]! =
    expandTree 6 1792 fourRows41[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row01 : fourWide41[1]! =
    expandTree 6 1792 fourRows41[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row02 : fourWide41[2]! =
    expandTree 6 1792 fourRows41[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row03 : fourWide41[3]! =
    expandTree 6 1792 fourRows41[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row04 : fourWide41[4]! =
    expandTree 6 1792 fourRows41[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row05 : fourWide41[5]! =
    expandTree 6 1792 fourRows41[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row06 : fourWide41[6]! =
    expandTree 6 1792 fourRows41[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row07 : fourWide41[7]! =
    expandTree 6 1792 fourRows41[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row08 : fourWide41[8]! =
    expandTree 6 1792 fourRows41[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row09 : fourWide41[9]! =
    expandTree 6 1792 fourRows41[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row10 : fourWide41[10]! =
    expandTree 6 1792 fourRows41[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row11 : fourWide41[11]! =
    expandTree 6 1792 fourRows41[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row12 : fourWide41[12]! =
    expandTree 6 1792 fourRows41[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row13 : fourWide41[13]! =
    expandTree 6 1792 fourRows41[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row14 : fourWide41[14]! =
    expandTree 6 1792 fourRows41[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row15 : fourWide41[15]! =
    expandTree 6 1792 fourRows41[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row16 : fourWide41[16]! =
    expandTree 6 1792 fourRows41[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row17 : fourWide41[17]! =
    expandTree 6 1792 fourRows41[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row18 : fourWide41[18]! =
    expandTree 6 1792 fourRows41[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row19 : fourWide41[19]! =
    expandTree 6 1792 fourRows41[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row20 : fourWide41[20]! =
    expandTree 6 1792 fourRows41[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row21 : fourWide41[21]! =
    expandTree 6 1792 fourRows41[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row22 : fourWide41[22]! =
    expandTree 6 1792 fourRows41[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row23 : fourWide41[23]! =
    expandTree 6 1792 fourRows41[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row24 : fourWide41[24]! =
    expandTree 6 1792 fourRows41[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row25 : fourWide41[25]! =
    expandTree 6 1792 fourRows41[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row26 : fourWide41[26]! =
    expandTree 6 1792 fourRows41[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row27 : fourWide41[27]! =
    expandTree 6 1792 fourRows41[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row28 : fourWide41[28]! =
    expandTree 6 1792 fourRows41[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row29 : fourWide41[29]! =
    expandTree 6 1792 fourRows41[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row30 : fourWide41[30]! =
    expandTree 6 1792 fourRows41[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded41_row31 : fourWide41[31]! =
    expandTree 6 1792 fourRows41[31]! := by decide +kernel

private theorem expanded41 : fourWide41 =
    fourRows41.map (expandTree 6 1792) := by
  change [fourWide41[0]!,
    fourWide41[1]!,
    fourWide41[2]!,
    fourWide41[3]!,
    fourWide41[4]!,
    fourWide41[5]!,
    fourWide41[6]!,
    fourWide41[7]!,
    fourWide41[8]!,
    fourWide41[9]!,
    fourWide41[10]!,
    fourWide41[11]!,
    fourWide41[12]!,
    fourWide41[13]!,
    fourWide41[14]!,
    fourWide41[15]!,
    fourWide41[16]!,
    fourWide41[17]!,
    fourWide41[18]!,
    fourWide41[19]!,
    fourWide41[20]!,
    fourWide41[21]!,
    fourWide41[22]!,
    fourWide41[23]!,
    fourWide41[24]!,
    fourWide41[25]!,
    fourWide41[26]!,
    fourWide41[27]!,
    fourWide41[28]!,
    fourWide41[29]!,
    fourWide41[30]!,
    fourWide41[31]!] =
    [expandTree 6 1792 fourRows41[0]!,
     expandTree 6 1792 fourRows41[1]!,
     expandTree 6 1792 fourRows41[2]!,
     expandTree 6 1792 fourRows41[3]!,
     expandTree 6 1792 fourRows41[4]!,
     expandTree 6 1792 fourRows41[5]!,
     expandTree 6 1792 fourRows41[6]!,
     expandTree 6 1792 fourRows41[7]!,
     expandTree 6 1792 fourRows41[8]!,
     expandTree 6 1792 fourRows41[9]!,
     expandTree 6 1792 fourRows41[10]!,
     expandTree 6 1792 fourRows41[11]!,
     expandTree 6 1792 fourRows41[12]!,
     expandTree 6 1792 fourRows41[13]!,
     expandTree 6 1792 fourRows41[14]!,
     expandTree 6 1792 fourRows41[15]!,
     expandTree 6 1792 fourRows41[16]!,
     expandTree 6 1792 fourRows41[17]!,
     expandTree 6 1792 fourRows41[18]!,
     expandTree 6 1792 fourRows41[19]!,
     expandTree 6 1792 fourRows41[20]!,
     expandTree 6 1792 fourRows41[21]!,
     expandTree 6 1792 fourRows41[22]!,
     expandTree 6 1792 fourRows41[23]!,
     expandTree 6 1792 fourRows41[24]!,
     expandTree 6 1792 fourRows41[25]!,
     expandTree 6 1792 fourRows41[26]!,
     expandTree 6 1792 fourRows41[27]!,
     expandTree 6 1792 fourRows41[28]!,
     expandTree 6 1792 fourRows41[29]!,
     expandTree 6 1792 fourRows41[30]!,
     expandTree 6 1792 fourRows41[31]!]
  rw [expanded41_row00, expanded41_row01, expanded41_row02, expanded41_row03, expanded41_row04, expanded41_row05, expanded41_row06, expanded41_row07, expanded41_row08, expanded41_row09, expanded41_row10, expanded41_row11, expanded41_row12, expanded41_row13, expanded41_row14, expanded41_row15, expanded41_row16, expanded41_row17, expanded41_row18, expanded41_row19, expanded41_row20, expanded41_row21, expanded41_row22, expanded41_row23, expanded41_row24, expanded41_row25, expanded41_row26, expanded41_row27, expanded41_row28, expanded41_row29, expanded41_row30, expanded41_row31]

set_option maxRecDepth 8192 in
private theorem expanded42_row00 : fourWide42[0]! =
    expandTree 6 1792 fourRows42[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row01 : fourWide42[1]! =
    expandTree 6 1792 fourRows42[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row02 : fourWide42[2]! =
    expandTree 6 1792 fourRows42[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row03 : fourWide42[3]! =
    expandTree 6 1792 fourRows42[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row04 : fourWide42[4]! =
    expandTree 6 1792 fourRows42[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row05 : fourWide42[5]! =
    expandTree 6 1792 fourRows42[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row06 : fourWide42[6]! =
    expandTree 6 1792 fourRows42[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row07 : fourWide42[7]! =
    expandTree 6 1792 fourRows42[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row08 : fourWide42[8]! =
    expandTree 6 1792 fourRows42[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row09 : fourWide42[9]! =
    expandTree 6 1792 fourRows42[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row10 : fourWide42[10]! =
    expandTree 6 1792 fourRows42[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row11 : fourWide42[11]! =
    expandTree 6 1792 fourRows42[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row12 : fourWide42[12]! =
    expandTree 6 1792 fourRows42[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row13 : fourWide42[13]! =
    expandTree 6 1792 fourRows42[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row14 : fourWide42[14]! =
    expandTree 6 1792 fourRows42[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row15 : fourWide42[15]! =
    expandTree 6 1792 fourRows42[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row16 : fourWide42[16]! =
    expandTree 6 1792 fourRows42[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row17 : fourWide42[17]! =
    expandTree 6 1792 fourRows42[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row18 : fourWide42[18]! =
    expandTree 6 1792 fourRows42[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row19 : fourWide42[19]! =
    expandTree 6 1792 fourRows42[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row20 : fourWide42[20]! =
    expandTree 6 1792 fourRows42[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row21 : fourWide42[21]! =
    expandTree 6 1792 fourRows42[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row22 : fourWide42[22]! =
    expandTree 6 1792 fourRows42[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row23 : fourWide42[23]! =
    expandTree 6 1792 fourRows42[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row24 : fourWide42[24]! =
    expandTree 6 1792 fourRows42[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row25 : fourWide42[25]! =
    expandTree 6 1792 fourRows42[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row26 : fourWide42[26]! =
    expandTree 6 1792 fourRows42[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row27 : fourWide42[27]! =
    expandTree 6 1792 fourRows42[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row28 : fourWide42[28]! =
    expandTree 6 1792 fourRows42[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row29 : fourWide42[29]! =
    expandTree 6 1792 fourRows42[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row30 : fourWide42[30]! =
    expandTree 6 1792 fourRows42[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded42_row31 : fourWide42[31]! =
    expandTree 6 1792 fourRows42[31]! := by decide +kernel

private theorem expanded42 : fourWide42 =
    fourRows42.map (expandTree 6 1792) := by
  change [fourWide42[0]!,
    fourWide42[1]!,
    fourWide42[2]!,
    fourWide42[3]!,
    fourWide42[4]!,
    fourWide42[5]!,
    fourWide42[6]!,
    fourWide42[7]!,
    fourWide42[8]!,
    fourWide42[9]!,
    fourWide42[10]!,
    fourWide42[11]!,
    fourWide42[12]!,
    fourWide42[13]!,
    fourWide42[14]!,
    fourWide42[15]!,
    fourWide42[16]!,
    fourWide42[17]!,
    fourWide42[18]!,
    fourWide42[19]!,
    fourWide42[20]!,
    fourWide42[21]!,
    fourWide42[22]!,
    fourWide42[23]!,
    fourWide42[24]!,
    fourWide42[25]!,
    fourWide42[26]!,
    fourWide42[27]!,
    fourWide42[28]!,
    fourWide42[29]!,
    fourWide42[30]!,
    fourWide42[31]!] =
    [expandTree 6 1792 fourRows42[0]!,
     expandTree 6 1792 fourRows42[1]!,
     expandTree 6 1792 fourRows42[2]!,
     expandTree 6 1792 fourRows42[3]!,
     expandTree 6 1792 fourRows42[4]!,
     expandTree 6 1792 fourRows42[5]!,
     expandTree 6 1792 fourRows42[6]!,
     expandTree 6 1792 fourRows42[7]!,
     expandTree 6 1792 fourRows42[8]!,
     expandTree 6 1792 fourRows42[9]!,
     expandTree 6 1792 fourRows42[10]!,
     expandTree 6 1792 fourRows42[11]!,
     expandTree 6 1792 fourRows42[12]!,
     expandTree 6 1792 fourRows42[13]!,
     expandTree 6 1792 fourRows42[14]!,
     expandTree 6 1792 fourRows42[15]!,
     expandTree 6 1792 fourRows42[16]!,
     expandTree 6 1792 fourRows42[17]!,
     expandTree 6 1792 fourRows42[18]!,
     expandTree 6 1792 fourRows42[19]!,
     expandTree 6 1792 fourRows42[20]!,
     expandTree 6 1792 fourRows42[21]!,
     expandTree 6 1792 fourRows42[22]!,
     expandTree 6 1792 fourRows42[23]!,
     expandTree 6 1792 fourRows42[24]!,
     expandTree 6 1792 fourRows42[25]!,
     expandTree 6 1792 fourRows42[26]!,
     expandTree 6 1792 fourRows42[27]!,
     expandTree 6 1792 fourRows42[28]!,
     expandTree 6 1792 fourRows42[29]!,
     expandTree 6 1792 fourRows42[30]!,
     expandTree 6 1792 fourRows42[31]!]
  rw [expanded42_row00, expanded42_row01, expanded42_row02, expanded42_row03, expanded42_row04, expanded42_row05, expanded42_row06, expanded42_row07, expanded42_row08, expanded42_row09, expanded42_row10, expanded42_row11, expanded42_row12, expanded42_row13, expanded42_row14, expanded42_row15, expanded42_row16, expanded42_row17, expanded42_row18, expanded42_row19, expanded42_row20, expanded42_row21, expanded42_row22, expanded42_row23, expanded42_row24, expanded42_row25, expanded42_row26, expanded42_row27, expanded42_row28, expanded42_row29, expanded42_row30, expanded42_row31]

set_option maxRecDepth 8192 in
private theorem expanded43_row00 : fourWide43[0]! =
    expandTree 6 1792 fourRows43[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row01 : fourWide43[1]! =
    expandTree 6 1792 fourRows43[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row02 : fourWide43[2]! =
    expandTree 6 1792 fourRows43[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row03 : fourWide43[3]! =
    expandTree 6 1792 fourRows43[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row04 : fourWide43[4]! =
    expandTree 6 1792 fourRows43[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row05 : fourWide43[5]! =
    expandTree 6 1792 fourRows43[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row06 : fourWide43[6]! =
    expandTree 6 1792 fourRows43[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row07 : fourWide43[7]! =
    expandTree 6 1792 fourRows43[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row08 : fourWide43[8]! =
    expandTree 6 1792 fourRows43[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row09 : fourWide43[9]! =
    expandTree 6 1792 fourRows43[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row10 : fourWide43[10]! =
    expandTree 6 1792 fourRows43[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row11 : fourWide43[11]! =
    expandTree 6 1792 fourRows43[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row12 : fourWide43[12]! =
    expandTree 6 1792 fourRows43[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row13 : fourWide43[13]! =
    expandTree 6 1792 fourRows43[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row14 : fourWide43[14]! =
    expandTree 6 1792 fourRows43[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row15 : fourWide43[15]! =
    expandTree 6 1792 fourRows43[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row16 : fourWide43[16]! =
    expandTree 6 1792 fourRows43[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row17 : fourWide43[17]! =
    expandTree 6 1792 fourRows43[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row18 : fourWide43[18]! =
    expandTree 6 1792 fourRows43[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row19 : fourWide43[19]! =
    expandTree 6 1792 fourRows43[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row20 : fourWide43[20]! =
    expandTree 6 1792 fourRows43[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row21 : fourWide43[21]! =
    expandTree 6 1792 fourRows43[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row22 : fourWide43[22]! =
    expandTree 6 1792 fourRows43[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row23 : fourWide43[23]! =
    expandTree 6 1792 fourRows43[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row24 : fourWide43[24]! =
    expandTree 6 1792 fourRows43[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row25 : fourWide43[25]! =
    expandTree 6 1792 fourRows43[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row26 : fourWide43[26]! =
    expandTree 6 1792 fourRows43[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row27 : fourWide43[27]! =
    expandTree 6 1792 fourRows43[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row28 : fourWide43[28]! =
    expandTree 6 1792 fourRows43[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row29 : fourWide43[29]! =
    expandTree 6 1792 fourRows43[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row30 : fourWide43[30]! =
    expandTree 6 1792 fourRows43[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded43_row31 : fourWide43[31]! =
    expandTree 6 1792 fourRows43[31]! := by decide +kernel

private theorem expanded43 : fourWide43 =
    fourRows43.map (expandTree 6 1792) := by
  change [fourWide43[0]!,
    fourWide43[1]!,
    fourWide43[2]!,
    fourWide43[3]!,
    fourWide43[4]!,
    fourWide43[5]!,
    fourWide43[6]!,
    fourWide43[7]!,
    fourWide43[8]!,
    fourWide43[9]!,
    fourWide43[10]!,
    fourWide43[11]!,
    fourWide43[12]!,
    fourWide43[13]!,
    fourWide43[14]!,
    fourWide43[15]!,
    fourWide43[16]!,
    fourWide43[17]!,
    fourWide43[18]!,
    fourWide43[19]!,
    fourWide43[20]!,
    fourWide43[21]!,
    fourWide43[22]!,
    fourWide43[23]!,
    fourWide43[24]!,
    fourWide43[25]!,
    fourWide43[26]!,
    fourWide43[27]!,
    fourWide43[28]!,
    fourWide43[29]!,
    fourWide43[30]!,
    fourWide43[31]!] =
    [expandTree 6 1792 fourRows43[0]!,
     expandTree 6 1792 fourRows43[1]!,
     expandTree 6 1792 fourRows43[2]!,
     expandTree 6 1792 fourRows43[3]!,
     expandTree 6 1792 fourRows43[4]!,
     expandTree 6 1792 fourRows43[5]!,
     expandTree 6 1792 fourRows43[6]!,
     expandTree 6 1792 fourRows43[7]!,
     expandTree 6 1792 fourRows43[8]!,
     expandTree 6 1792 fourRows43[9]!,
     expandTree 6 1792 fourRows43[10]!,
     expandTree 6 1792 fourRows43[11]!,
     expandTree 6 1792 fourRows43[12]!,
     expandTree 6 1792 fourRows43[13]!,
     expandTree 6 1792 fourRows43[14]!,
     expandTree 6 1792 fourRows43[15]!,
     expandTree 6 1792 fourRows43[16]!,
     expandTree 6 1792 fourRows43[17]!,
     expandTree 6 1792 fourRows43[18]!,
     expandTree 6 1792 fourRows43[19]!,
     expandTree 6 1792 fourRows43[20]!,
     expandTree 6 1792 fourRows43[21]!,
     expandTree 6 1792 fourRows43[22]!,
     expandTree 6 1792 fourRows43[23]!,
     expandTree 6 1792 fourRows43[24]!,
     expandTree 6 1792 fourRows43[25]!,
     expandTree 6 1792 fourRows43[26]!,
     expandTree 6 1792 fourRows43[27]!,
     expandTree 6 1792 fourRows43[28]!,
     expandTree 6 1792 fourRows43[29]!,
     expandTree 6 1792 fourRows43[30]!,
     expandTree 6 1792 fourRows43[31]!]
  rw [expanded43_row00, expanded43_row01, expanded43_row02, expanded43_row03, expanded43_row04, expanded43_row05, expanded43_row06, expanded43_row07, expanded43_row08, expanded43_row09, expanded43_row10, expanded43_row11, expanded43_row12, expanded43_row13, expanded43_row14, expanded43_row15, expanded43_row16, expanded43_row17, expanded43_row18, expanded43_row19, expanded43_row20, expanded43_row21, expanded43_row22, expanded43_row23, expanded43_row24, expanded43_row25, expanded43_row26, expanded43_row27, expanded43_row28, expanded43_row29, expanded43_row30, expanded43_row31]

set_option maxRecDepth 8192 in
private theorem expanded44_row00 : fourWide44[0]! =
    expandTree 6 1792 fourRows44[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row01 : fourWide44[1]! =
    expandTree 6 1792 fourRows44[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row02 : fourWide44[2]! =
    expandTree 6 1792 fourRows44[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row03 : fourWide44[3]! =
    expandTree 6 1792 fourRows44[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row04 : fourWide44[4]! =
    expandTree 6 1792 fourRows44[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row05 : fourWide44[5]! =
    expandTree 6 1792 fourRows44[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row06 : fourWide44[6]! =
    expandTree 6 1792 fourRows44[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row07 : fourWide44[7]! =
    expandTree 6 1792 fourRows44[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row08 : fourWide44[8]! =
    expandTree 6 1792 fourRows44[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row09 : fourWide44[9]! =
    expandTree 6 1792 fourRows44[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row10 : fourWide44[10]! =
    expandTree 6 1792 fourRows44[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row11 : fourWide44[11]! =
    expandTree 6 1792 fourRows44[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row12 : fourWide44[12]! =
    expandTree 6 1792 fourRows44[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row13 : fourWide44[13]! =
    expandTree 6 1792 fourRows44[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row14 : fourWide44[14]! =
    expandTree 6 1792 fourRows44[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row15 : fourWide44[15]! =
    expandTree 6 1792 fourRows44[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row16 : fourWide44[16]! =
    expandTree 6 1792 fourRows44[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row17 : fourWide44[17]! =
    expandTree 6 1792 fourRows44[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row18 : fourWide44[18]! =
    expandTree 6 1792 fourRows44[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row19 : fourWide44[19]! =
    expandTree 6 1792 fourRows44[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row20 : fourWide44[20]! =
    expandTree 6 1792 fourRows44[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row21 : fourWide44[21]! =
    expandTree 6 1792 fourRows44[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row22 : fourWide44[22]! =
    expandTree 6 1792 fourRows44[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row23 : fourWide44[23]! =
    expandTree 6 1792 fourRows44[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row24 : fourWide44[24]! =
    expandTree 6 1792 fourRows44[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row25 : fourWide44[25]! =
    expandTree 6 1792 fourRows44[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row26 : fourWide44[26]! =
    expandTree 6 1792 fourRows44[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row27 : fourWide44[27]! =
    expandTree 6 1792 fourRows44[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row28 : fourWide44[28]! =
    expandTree 6 1792 fourRows44[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row29 : fourWide44[29]! =
    expandTree 6 1792 fourRows44[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row30 : fourWide44[30]! =
    expandTree 6 1792 fourRows44[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded44_row31 : fourWide44[31]! =
    expandTree 6 1792 fourRows44[31]! := by decide +kernel

private theorem expanded44 : fourWide44 =
    fourRows44.map (expandTree 6 1792) := by
  change [fourWide44[0]!,
    fourWide44[1]!,
    fourWide44[2]!,
    fourWide44[3]!,
    fourWide44[4]!,
    fourWide44[5]!,
    fourWide44[6]!,
    fourWide44[7]!,
    fourWide44[8]!,
    fourWide44[9]!,
    fourWide44[10]!,
    fourWide44[11]!,
    fourWide44[12]!,
    fourWide44[13]!,
    fourWide44[14]!,
    fourWide44[15]!,
    fourWide44[16]!,
    fourWide44[17]!,
    fourWide44[18]!,
    fourWide44[19]!,
    fourWide44[20]!,
    fourWide44[21]!,
    fourWide44[22]!,
    fourWide44[23]!,
    fourWide44[24]!,
    fourWide44[25]!,
    fourWide44[26]!,
    fourWide44[27]!,
    fourWide44[28]!,
    fourWide44[29]!,
    fourWide44[30]!,
    fourWide44[31]!] =
    [expandTree 6 1792 fourRows44[0]!,
     expandTree 6 1792 fourRows44[1]!,
     expandTree 6 1792 fourRows44[2]!,
     expandTree 6 1792 fourRows44[3]!,
     expandTree 6 1792 fourRows44[4]!,
     expandTree 6 1792 fourRows44[5]!,
     expandTree 6 1792 fourRows44[6]!,
     expandTree 6 1792 fourRows44[7]!,
     expandTree 6 1792 fourRows44[8]!,
     expandTree 6 1792 fourRows44[9]!,
     expandTree 6 1792 fourRows44[10]!,
     expandTree 6 1792 fourRows44[11]!,
     expandTree 6 1792 fourRows44[12]!,
     expandTree 6 1792 fourRows44[13]!,
     expandTree 6 1792 fourRows44[14]!,
     expandTree 6 1792 fourRows44[15]!,
     expandTree 6 1792 fourRows44[16]!,
     expandTree 6 1792 fourRows44[17]!,
     expandTree 6 1792 fourRows44[18]!,
     expandTree 6 1792 fourRows44[19]!,
     expandTree 6 1792 fourRows44[20]!,
     expandTree 6 1792 fourRows44[21]!,
     expandTree 6 1792 fourRows44[22]!,
     expandTree 6 1792 fourRows44[23]!,
     expandTree 6 1792 fourRows44[24]!,
     expandTree 6 1792 fourRows44[25]!,
     expandTree 6 1792 fourRows44[26]!,
     expandTree 6 1792 fourRows44[27]!,
     expandTree 6 1792 fourRows44[28]!,
     expandTree 6 1792 fourRows44[29]!,
     expandTree 6 1792 fourRows44[30]!,
     expandTree 6 1792 fourRows44[31]!]
  rw [expanded44_row00, expanded44_row01, expanded44_row02, expanded44_row03, expanded44_row04, expanded44_row05, expanded44_row06, expanded44_row07, expanded44_row08, expanded44_row09, expanded44_row10, expanded44_row11, expanded44_row12, expanded44_row13, expanded44_row14, expanded44_row15, expanded44_row16, expanded44_row17, expanded44_row18, expanded44_row19, expanded44_row20, expanded44_row21, expanded44_row22, expanded44_row23, expanded44_row24, expanded44_row25, expanded44_row26, expanded44_row27, expanded44_row28, expanded44_row29, expanded44_row30, expanded44_row31]

set_option maxRecDepth 8192 in
private theorem expanded45_row00 : fourWide45[0]! =
    expandTree 6 1792 fourRows45[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row01 : fourWide45[1]! =
    expandTree 6 1792 fourRows45[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row02 : fourWide45[2]! =
    expandTree 6 1792 fourRows45[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row03 : fourWide45[3]! =
    expandTree 6 1792 fourRows45[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row04 : fourWide45[4]! =
    expandTree 6 1792 fourRows45[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row05 : fourWide45[5]! =
    expandTree 6 1792 fourRows45[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row06 : fourWide45[6]! =
    expandTree 6 1792 fourRows45[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row07 : fourWide45[7]! =
    expandTree 6 1792 fourRows45[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row08 : fourWide45[8]! =
    expandTree 6 1792 fourRows45[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row09 : fourWide45[9]! =
    expandTree 6 1792 fourRows45[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row10 : fourWide45[10]! =
    expandTree 6 1792 fourRows45[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row11 : fourWide45[11]! =
    expandTree 6 1792 fourRows45[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row12 : fourWide45[12]! =
    expandTree 6 1792 fourRows45[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row13 : fourWide45[13]! =
    expandTree 6 1792 fourRows45[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row14 : fourWide45[14]! =
    expandTree 6 1792 fourRows45[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row15 : fourWide45[15]! =
    expandTree 6 1792 fourRows45[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row16 : fourWide45[16]! =
    expandTree 6 1792 fourRows45[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row17 : fourWide45[17]! =
    expandTree 6 1792 fourRows45[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row18 : fourWide45[18]! =
    expandTree 6 1792 fourRows45[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row19 : fourWide45[19]! =
    expandTree 6 1792 fourRows45[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row20 : fourWide45[20]! =
    expandTree 6 1792 fourRows45[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row21 : fourWide45[21]! =
    expandTree 6 1792 fourRows45[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row22 : fourWide45[22]! =
    expandTree 6 1792 fourRows45[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row23 : fourWide45[23]! =
    expandTree 6 1792 fourRows45[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row24 : fourWide45[24]! =
    expandTree 6 1792 fourRows45[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row25 : fourWide45[25]! =
    expandTree 6 1792 fourRows45[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row26 : fourWide45[26]! =
    expandTree 6 1792 fourRows45[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row27 : fourWide45[27]! =
    expandTree 6 1792 fourRows45[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row28 : fourWide45[28]! =
    expandTree 6 1792 fourRows45[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row29 : fourWide45[29]! =
    expandTree 6 1792 fourRows45[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row30 : fourWide45[30]! =
    expandTree 6 1792 fourRows45[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded45_row31 : fourWide45[31]! =
    expandTree 6 1792 fourRows45[31]! := by decide +kernel

private theorem expanded45 : fourWide45 =
    fourRows45.map (expandTree 6 1792) := by
  change [fourWide45[0]!,
    fourWide45[1]!,
    fourWide45[2]!,
    fourWide45[3]!,
    fourWide45[4]!,
    fourWide45[5]!,
    fourWide45[6]!,
    fourWide45[7]!,
    fourWide45[8]!,
    fourWide45[9]!,
    fourWide45[10]!,
    fourWide45[11]!,
    fourWide45[12]!,
    fourWide45[13]!,
    fourWide45[14]!,
    fourWide45[15]!,
    fourWide45[16]!,
    fourWide45[17]!,
    fourWide45[18]!,
    fourWide45[19]!,
    fourWide45[20]!,
    fourWide45[21]!,
    fourWide45[22]!,
    fourWide45[23]!,
    fourWide45[24]!,
    fourWide45[25]!,
    fourWide45[26]!,
    fourWide45[27]!,
    fourWide45[28]!,
    fourWide45[29]!,
    fourWide45[30]!,
    fourWide45[31]!] =
    [expandTree 6 1792 fourRows45[0]!,
     expandTree 6 1792 fourRows45[1]!,
     expandTree 6 1792 fourRows45[2]!,
     expandTree 6 1792 fourRows45[3]!,
     expandTree 6 1792 fourRows45[4]!,
     expandTree 6 1792 fourRows45[5]!,
     expandTree 6 1792 fourRows45[6]!,
     expandTree 6 1792 fourRows45[7]!,
     expandTree 6 1792 fourRows45[8]!,
     expandTree 6 1792 fourRows45[9]!,
     expandTree 6 1792 fourRows45[10]!,
     expandTree 6 1792 fourRows45[11]!,
     expandTree 6 1792 fourRows45[12]!,
     expandTree 6 1792 fourRows45[13]!,
     expandTree 6 1792 fourRows45[14]!,
     expandTree 6 1792 fourRows45[15]!,
     expandTree 6 1792 fourRows45[16]!,
     expandTree 6 1792 fourRows45[17]!,
     expandTree 6 1792 fourRows45[18]!,
     expandTree 6 1792 fourRows45[19]!,
     expandTree 6 1792 fourRows45[20]!,
     expandTree 6 1792 fourRows45[21]!,
     expandTree 6 1792 fourRows45[22]!,
     expandTree 6 1792 fourRows45[23]!,
     expandTree 6 1792 fourRows45[24]!,
     expandTree 6 1792 fourRows45[25]!,
     expandTree 6 1792 fourRows45[26]!,
     expandTree 6 1792 fourRows45[27]!,
     expandTree 6 1792 fourRows45[28]!,
     expandTree 6 1792 fourRows45[29]!,
     expandTree 6 1792 fourRows45[30]!,
     expandTree 6 1792 fourRows45[31]!]
  rw [expanded45_row00, expanded45_row01, expanded45_row02, expanded45_row03, expanded45_row04, expanded45_row05, expanded45_row06, expanded45_row07, expanded45_row08, expanded45_row09, expanded45_row10, expanded45_row11, expanded45_row12, expanded45_row13, expanded45_row14, expanded45_row15, expanded45_row16, expanded45_row17, expanded45_row18, expanded45_row19, expanded45_row20, expanded45_row21, expanded45_row22, expanded45_row23, expanded45_row24, expanded45_row25, expanded45_row26, expanded45_row27, expanded45_row28, expanded45_row29, expanded45_row30, expanded45_row31]

set_option maxRecDepth 8192 in
private theorem expanded46_row00 : fourWide46[0]! =
    expandTree 6 1792 fourRows46[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row01 : fourWide46[1]! =
    expandTree 6 1792 fourRows46[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row02 : fourWide46[2]! =
    expandTree 6 1792 fourRows46[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row03 : fourWide46[3]! =
    expandTree 6 1792 fourRows46[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row04 : fourWide46[4]! =
    expandTree 6 1792 fourRows46[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row05 : fourWide46[5]! =
    expandTree 6 1792 fourRows46[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row06 : fourWide46[6]! =
    expandTree 6 1792 fourRows46[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row07 : fourWide46[7]! =
    expandTree 6 1792 fourRows46[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row08 : fourWide46[8]! =
    expandTree 6 1792 fourRows46[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row09 : fourWide46[9]! =
    expandTree 6 1792 fourRows46[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row10 : fourWide46[10]! =
    expandTree 6 1792 fourRows46[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row11 : fourWide46[11]! =
    expandTree 6 1792 fourRows46[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row12 : fourWide46[12]! =
    expandTree 6 1792 fourRows46[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row13 : fourWide46[13]! =
    expandTree 6 1792 fourRows46[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row14 : fourWide46[14]! =
    expandTree 6 1792 fourRows46[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row15 : fourWide46[15]! =
    expandTree 6 1792 fourRows46[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row16 : fourWide46[16]! =
    expandTree 6 1792 fourRows46[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row17 : fourWide46[17]! =
    expandTree 6 1792 fourRows46[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row18 : fourWide46[18]! =
    expandTree 6 1792 fourRows46[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row19 : fourWide46[19]! =
    expandTree 6 1792 fourRows46[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row20 : fourWide46[20]! =
    expandTree 6 1792 fourRows46[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row21 : fourWide46[21]! =
    expandTree 6 1792 fourRows46[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row22 : fourWide46[22]! =
    expandTree 6 1792 fourRows46[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row23 : fourWide46[23]! =
    expandTree 6 1792 fourRows46[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row24 : fourWide46[24]! =
    expandTree 6 1792 fourRows46[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row25 : fourWide46[25]! =
    expandTree 6 1792 fourRows46[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row26 : fourWide46[26]! =
    expandTree 6 1792 fourRows46[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row27 : fourWide46[27]! =
    expandTree 6 1792 fourRows46[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row28 : fourWide46[28]! =
    expandTree 6 1792 fourRows46[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row29 : fourWide46[29]! =
    expandTree 6 1792 fourRows46[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row30 : fourWide46[30]! =
    expandTree 6 1792 fourRows46[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded46_row31 : fourWide46[31]! =
    expandTree 6 1792 fourRows46[31]! := by decide +kernel

private theorem expanded46 : fourWide46 =
    fourRows46.map (expandTree 6 1792) := by
  change [fourWide46[0]!,
    fourWide46[1]!,
    fourWide46[2]!,
    fourWide46[3]!,
    fourWide46[4]!,
    fourWide46[5]!,
    fourWide46[6]!,
    fourWide46[7]!,
    fourWide46[8]!,
    fourWide46[9]!,
    fourWide46[10]!,
    fourWide46[11]!,
    fourWide46[12]!,
    fourWide46[13]!,
    fourWide46[14]!,
    fourWide46[15]!,
    fourWide46[16]!,
    fourWide46[17]!,
    fourWide46[18]!,
    fourWide46[19]!,
    fourWide46[20]!,
    fourWide46[21]!,
    fourWide46[22]!,
    fourWide46[23]!,
    fourWide46[24]!,
    fourWide46[25]!,
    fourWide46[26]!,
    fourWide46[27]!,
    fourWide46[28]!,
    fourWide46[29]!,
    fourWide46[30]!,
    fourWide46[31]!] =
    [expandTree 6 1792 fourRows46[0]!,
     expandTree 6 1792 fourRows46[1]!,
     expandTree 6 1792 fourRows46[2]!,
     expandTree 6 1792 fourRows46[3]!,
     expandTree 6 1792 fourRows46[4]!,
     expandTree 6 1792 fourRows46[5]!,
     expandTree 6 1792 fourRows46[6]!,
     expandTree 6 1792 fourRows46[7]!,
     expandTree 6 1792 fourRows46[8]!,
     expandTree 6 1792 fourRows46[9]!,
     expandTree 6 1792 fourRows46[10]!,
     expandTree 6 1792 fourRows46[11]!,
     expandTree 6 1792 fourRows46[12]!,
     expandTree 6 1792 fourRows46[13]!,
     expandTree 6 1792 fourRows46[14]!,
     expandTree 6 1792 fourRows46[15]!,
     expandTree 6 1792 fourRows46[16]!,
     expandTree 6 1792 fourRows46[17]!,
     expandTree 6 1792 fourRows46[18]!,
     expandTree 6 1792 fourRows46[19]!,
     expandTree 6 1792 fourRows46[20]!,
     expandTree 6 1792 fourRows46[21]!,
     expandTree 6 1792 fourRows46[22]!,
     expandTree 6 1792 fourRows46[23]!,
     expandTree 6 1792 fourRows46[24]!,
     expandTree 6 1792 fourRows46[25]!,
     expandTree 6 1792 fourRows46[26]!,
     expandTree 6 1792 fourRows46[27]!,
     expandTree 6 1792 fourRows46[28]!,
     expandTree 6 1792 fourRows46[29]!,
     expandTree 6 1792 fourRows46[30]!,
     expandTree 6 1792 fourRows46[31]!]
  rw [expanded46_row00, expanded46_row01, expanded46_row02, expanded46_row03, expanded46_row04, expanded46_row05, expanded46_row06, expanded46_row07, expanded46_row08, expanded46_row09, expanded46_row10, expanded46_row11, expanded46_row12, expanded46_row13, expanded46_row14, expanded46_row15, expanded46_row16, expanded46_row17, expanded46_row18, expanded46_row19, expanded46_row20, expanded46_row21, expanded46_row22, expanded46_row23, expanded46_row24, expanded46_row25, expanded46_row26, expanded46_row27, expanded46_row28, expanded46_row29, expanded46_row30, expanded46_row31]

set_option maxRecDepth 8192 in
private theorem expanded47_row00 : fourWide47[0]! =
    expandTree 6 1792 fourRows47[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row01 : fourWide47[1]! =
    expandTree 6 1792 fourRows47[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row02 : fourWide47[2]! =
    expandTree 6 1792 fourRows47[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row03 : fourWide47[3]! =
    expandTree 6 1792 fourRows47[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row04 : fourWide47[4]! =
    expandTree 6 1792 fourRows47[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row05 : fourWide47[5]! =
    expandTree 6 1792 fourRows47[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row06 : fourWide47[6]! =
    expandTree 6 1792 fourRows47[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row07 : fourWide47[7]! =
    expandTree 6 1792 fourRows47[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row08 : fourWide47[8]! =
    expandTree 6 1792 fourRows47[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row09 : fourWide47[9]! =
    expandTree 6 1792 fourRows47[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row10 : fourWide47[10]! =
    expandTree 6 1792 fourRows47[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row11 : fourWide47[11]! =
    expandTree 6 1792 fourRows47[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row12 : fourWide47[12]! =
    expandTree 6 1792 fourRows47[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row13 : fourWide47[13]! =
    expandTree 6 1792 fourRows47[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row14 : fourWide47[14]! =
    expandTree 6 1792 fourRows47[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row15 : fourWide47[15]! =
    expandTree 6 1792 fourRows47[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row16 : fourWide47[16]! =
    expandTree 6 1792 fourRows47[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row17 : fourWide47[17]! =
    expandTree 6 1792 fourRows47[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row18 : fourWide47[18]! =
    expandTree 6 1792 fourRows47[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row19 : fourWide47[19]! =
    expandTree 6 1792 fourRows47[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row20 : fourWide47[20]! =
    expandTree 6 1792 fourRows47[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row21 : fourWide47[21]! =
    expandTree 6 1792 fourRows47[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row22 : fourWide47[22]! =
    expandTree 6 1792 fourRows47[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row23 : fourWide47[23]! =
    expandTree 6 1792 fourRows47[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row24 : fourWide47[24]! =
    expandTree 6 1792 fourRows47[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row25 : fourWide47[25]! =
    expandTree 6 1792 fourRows47[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row26 : fourWide47[26]! =
    expandTree 6 1792 fourRows47[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row27 : fourWide47[27]! =
    expandTree 6 1792 fourRows47[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row28 : fourWide47[28]! =
    expandTree 6 1792 fourRows47[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row29 : fourWide47[29]! =
    expandTree 6 1792 fourRows47[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row30 : fourWide47[30]! =
    expandTree 6 1792 fourRows47[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded47_row31 : fourWide47[31]! =
    expandTree 6 1792 fourRows47[31]! := by decide +kernel

private theorem expanded47 : fourWide47 =
    fourRows47.map (expandTree 6 1792) := by
  change [fourWide47[0]!,
    fourWide47[1]!,
    fourWide47[2]!,
    fourWide47[3]!,
    fourWide47[4]!,
    fourWide47[5]!,
    fourWide47[6]!,
    fourWide47[7]!,
    fourWide47[8]!,
    fourWide47[9]!,
    fourWide47[10]!,
    fourWide47[11]!,
    fourWide47[12]!,
    fourWide47[13]!,
    fourWide47[14]!,
    fourWide47[15]!,
    fourWide47[16]!,
    fourWide47[17]!,
    fourWide47[18]!,
    fourWide47[19]!,
    fourWide47[20]!,
    fourWide47[21]!,
    fourWide47[22]!,
    fourWide47[23]!,
    fourWide47[24]!,
    fourWide47[25]!,
    fourWide47[26]!,
    fourWide47[27]!,
    fourWide47[28]!,
    fourWide47[29]!,
    fourWide47[30]!,
    fourWide47[31]!] =
    [expandTree 6 1792 fourRows47[0]!,
     expandTree 6 1792 fourRows47[1]!,
     expandTree 6 1792 fourRows47[2]!,
     expandTree 6 1792 fourRows47[3]!,
     expandTree 6 1792 fourRows47[4]!,
     expandTree 6 1792 fourRows47[5]!,
     expandTree 6 1792 fourRows47[6]!,
     expandTree 6 1792 fourRows47[7]!,
     expandTree 6 1792 fourRows47[8]!,
     expandTree 6 1792 fourRows47[9]!,
     expandTree 6 1792 fourRows47[10]!,
     expandTree 6 1792 fourRows47[11]!,
     expandTree 6 1792 fourRows47[12]!,
     expandTree 6 1792 fourRows47[13]!,
     expandTree 6 1792 fourRows47[14]!,
     expandTree 6 1792 fourRows47[15]!,
     expandTree 6 1792 fourRows47[16]!,
     expandTree 6 1792 fourRows47[17]!,
     expandTree 6 1792 fourRows47[18]!,
     expandTree 6 1792 fourRows47[19]!,
     expandTree 6 1792 fourRows47[20]!,
     expandTree 6 1792 fourRows47[21]!,
     expandTree 6 1792 fourRows47[22]!,
     expandTree 6 1792 fourRows47[23]!,
     expandTree 6 1792 fourRows47[24]!,
     expandTree 6 1792 fourRows47[25]!,
     expandTree 6 1792 fourRows47[26]!,
     expandTree 6 1792 fourRows47[27]!,
     expandTree 6 1792 fourRows47[28]!,
     expandTree 6 1792 fourRows47[29]!,
     expandTree 6 1792 fourRows47[30]!,
     expandTree 6 1792 fourRows47[31]!]
  rw [expanded47_row00, expanded47_row01, expanded47_row02, expanded47_row03, expanded47_row04, expanded47_row05, expanded47_row06, expanded47_row07, expanded47_row08, expanded47_row09, expanded47_row10, expanded47_row11, expanded47_row12, expanded47_row13, expanded47_row14, expanded47_row15, expanded47_row16, expanded47_row17, expanded47_row18, expanded47_row19, expanded47_row20, expanded47_row21, expanded47_row22, expanded47_row23, expanded47_row24, expanded47_row25, expanded47_row26, expanded47_row27, expanded47_row28, expanded47_row29, expanded47_row30, expanded47_row31]

set_option maxRecDepth 8192 in
private theorem expanded48_row00 : fourWide48[0]! =
    expandTree 6 1792 fourRows48[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row01 : fourWide48[1]! =
    expandTree 6 1792 fourRows48[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row02 : fourWide48[2]! =
    expandTree 6 1792 fourRows48[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row03 : fourWide48[3]! =
    expandTree 6 1792 fourRows48[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row04 : fourWide48[4]! =
    expandTree 6 1792 fourRows48[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row05 : fourWide48[5]! =
    expandTree 6 1792 fourRows48[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row06 : fourWide48[6]! =
    expandTree 6 1792 fourRows48[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row07 : fourWide48[7]! =
    expandTree 6 1792 fourRows48[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row08 : fourWide48[8]! =
    expandTree 6 1792 fourRows48[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row09 : fourWide48[9]! =
    expandTree 6 1792 fourRows48[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row10 : fourWide48[10]! =
    expandTree 6 1792 fourRows48[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row11 : fourWide48[11]! =
    expandTree 6 1792 fourRows48[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row12 : fourWide48[12]! =
    expandTree 6 1792 fourRows48[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row13 : fourWide48[13]! =
    expandTree 6 1792 fourRows48[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row14 : fourWide48[14]! =
    expandTree 6 1792 fourRows48[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row15 : fourWide48[15]! =
    expandTree 6 1792 fourRows48[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row16 : fourWide48[16]! =
    expandTree 6 1792 fourRows48[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row17 : fourWide48[17]! =
    expandTree 6 1792 fourRows48[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row18 : fourWide48[18]! =
    expandTree 6 1792 fourRows48[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row19 : fourWide48[19]! =
    expandTree 6 1792 fourRows48[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row20 : fourWide48[20]! =
    expandTree 6 1792 fourRows48[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row21 : fourWide48[21]! =
    expandTree 6 1792 fourRows48[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row22 : fourWide48[22]! =
    expandTree 6 1792 fourRows48[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row23 : fourWide48[23]! =
    expandTree 6 1792 fourRows48[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row24 : fourWide48[24]! =
    expandTree 6 1792 fourRows48[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row25 : fourWide48[25]! =
    expandTree 6 1792 fourRows48[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row26 : fourWide48[26]! =
    expandTree 6 1792 fourRows48[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row27 : fourWide48[27]! =
    expandTree 6 1792 fourRows48[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row28 : fourWide48[28]! =
    expandTree 6 1792 fourRows48[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row29 : fourWide48[29]! =
    expandTree 6 1792 fourRows48[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row30 : fourWide48[30]! =
    expandTree 6 1792 fourRows48[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded48_row31 : fourWide48[31]! =
    expandTree 6 1792 fourRows48[31]! := by decide +kernel

private theorem expanded48 : fourWide48 =
    fourRows48.map (expandTree 6 1792) := by
  change [fourWide48[0]!,
    fourWide48[1]!,
    fourWide48[2]!,
    fourWide48[3]!,
    fourWide48[4]!,
    fourWide48[5]!,
    fourWide48[6]!,
    fourWide48[7]!,
    fourWide48[8]!,
    fourWide48[9]!,
    fourWide48[10]!,
    fourWide48[11]!,
    fourWide48[12]!,
    fourWide48[13]!,
    fourWide48[14]!,
    fourWide48[15]!,
    fourWide48[16]!,
    fourWide48[17]!,
    fourWide48[18]!,
    fourWide48[19]!,
    fourWide48[20]!,
    fourWide48[21]!,
    fourWide48[22]!,
    fourWide48[23]!,
    fourWide48[24]!,
    fourWide48[25]!,
    fourWide48[26]!,
    fourWide48[27]!,
    fourWide48[28]!,
    fourWide48[29]!,
    fourWide48[30]!,
    fourWide48[31]!] =
    [expandTree 6 1792 fourRows48[0]!,
     expandTree 6 1792 fourRows48[1]!,
     expandTree 6 1792 fourRows48[2]!,
     expandTree 6 1792 fourRows48[3]!,
     expandTree 6 1792 fourRows48[4]!,
     expandTree 6 1792 fourRows48[5]!,
     expandTree 6 1792 fourRows48[6]!,
     expandTree 6 1792 fourRows48[7]!,
     expandTree 6 1792 fourRows48[8]!,
     expandTree 6 1792 fourRows48[9]!,
     expandTree 6 1792 fourRows48[10]!,
     expandTree 6 1792 fourRows48[11]!,
     expandTree 6 1792 fourRows48[12]!,
     expandTree 6 1792 fourRows48[13]!,
     expandTree 6 1792 fourRows48[14]!,
     expandTree 6 1792 fourRows48[15]!,
     expandTree 6 1792 fourRows48[16]!,
     expandTree 6 1792 fourRows48[17]!,
     expandTree 6 1792 fourRows48[18]!,
     expandTree 6 1792 fourRows48[19]!,
     expandTree 6 1792 fourRows48[20]!,
     expandTree 6 1792 fourRows48[21]!,
     expandTree 6 1792 fourRows48[22]!,
     expandTree 6 1792 fourRows48[23]!,
     expandTree 6 1792 fourRows48[24]!,
     expandTree 6 1792 fourRows48[25]!,
     expandTree 6 1792 fourRows48[26]!,
     expandTree 6 1792 fourRows48[27]!,
     expandTree 6 1792 fourRows48[28]!,
     expandTree 6 1792 fourRows48[29]!,
     expandTree 6 1792 fourRows48[30]!,
     expandTree 6 1792 fourRows48[31]!]
  rw [expanded48_row00, expanded48_row01, expanded48_row02, expanded48_row03, expanded48_row04, expanded48_row05, expanded48_row06, expanded48_row07, expanded48_row08, expanded48_row09, expanded48_row10, expanded48_row11, expanded48_row12, expanded48_row13, expanded48_row14, expanded48_row15, expanded48_row16, expanded48_row17, expanded48_row18, expanded48_row19, expanded48_row20, expanded48_row21, expanded48_row22, expanded48_row23, expanded48_row24, expanded48_row25, expanded48_row26, expanded48_row27, expanded48_row28, expanded48_row29, expanded48_row30, expanded48_row31]

set_option maxRecDepth 8192 in
private theorem expanded49_row00 : fourWide49[0]! =
    expandTree 6 1792 fourRows49[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row01 : fourWide49[1]! =
    expandTree 6 1792 fourRows49[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row02 : fourWide49[2]! =
    expandTree 6 1792 fourRows49[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row03 : fourWide49[3]! =
    expandTree 6 1792 fourRows49[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row04 : fourWide49[4]! =
    expandTree 6 1792 fourRows49[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row05 : fourWide49[5]! =
    expandTree 6 1792 fourRows49[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row06 : fourWide49[6]! =
    expandTree 6 1792 fourRows49[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row07 : fourWide49[7]! =
    expandTree 6 1792 fourRows49[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row08 : fourWide49[8]! =
    expandTree 6 1792 fourRows49[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row09 : fourWide49[9]! =
    expandTree 6 1792 fourRows49[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row10 : fourWide49[10]! =
    expandTree 6 1792 fourRows49[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row11 : fourWide49[11]! =
    expandTree 6 1792 fourRows49[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row12 : fourWide49[12]! =
    expandTree 6 1792 fourRows49[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row13 : fourWide49[13]! =
    expandTree 6 1792 fourRows49[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row14 : fourWide49[14]! =
    expandTree 6 1792 fourRows49[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row15 : fourWide49[15]! =
    expandTree 6 1792 fourRows49[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row16 : fourWide49[16]! =
    expandTree 6 1792 fourRows49[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row17 : fourWide49[17]! =
    expandTree 6 1792 fourRows49[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row18 : fourWide49[18]! =
    expandTree 6 1792 fourRows49[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row19 : fourWide49[19]! =
    expandTree 6 1792 fourRows49[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row20 : fourWide49[20]! =
    expandTree 6 1792 fourRows49[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row21 : fourWide49[21]! =
    expandTree 6 1792 fourRows49[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row22 : fourWide49[22]! =
    expandTree 6 1792 fourRows49[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row23 : fourWide49[23]! =
    expandTree 6 1792 fourRows49[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row24 : fourWide49[24]! =
    expandTree 6 1792 fourRows49[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row25 : fourWide49[25]! =
    expandTree 6 1792 fourRows49[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row26 : fourWide49[26]! =
    expandTree 6 1792 fourRows49[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row27 : fourWide49[27]! =
    expandTree 6 1792 fourRows49[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row28 : fourWide49[28]! =
    expandTree 6 1792 fourRows49[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row29 : fourWide49[29]! =
    expandTree 6 1792 fourRows49[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row30 : fourWide49[30]! =
    expandTree 6 1792 fourRows49[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded49_row31 : fourWide49[31]! =
    expandTree 6 1792 fourRows49[31]! := by decide +kernel

private theorem expanded49 : fourWide49 =
    fourRows49.map (expandTree 6 1792) := by
  change [fourWide49[0]!,
    fourWide49[1]!,
    fourWide49[2]!,
    fourWide49[3]!,
    fourWide49[4]!,
    fourWide49[5]!,
    fourWide49[6]!,
    fourWide49[7]!,
    fourWide49[8]!,
    fourWide49[9]!,
    fourWide49[10]!,
    fourWide49[11]!,
    fourWide49[12]!,
    fourWide49[13]!,
    fourWide49[14]!,
    fourWide49[15]!,
    fourWide49[16]!,
    fourWide49[17]!,
    fourWide49[18]!,
    fourWide49[19]!,
    fourWide49[20]!,
    fourWide49[21]!,
    fourWide49[22]!,
    fourWide49[23]!,
    fourWide49[24]!,
    fourWide49[25]!,
    fourWide49[26]!,
    fourWide49[27]!,
    fourWide49[28]!,
    fourWide49[29]!,
    fourWide49[30]!,
    fourWide49[31]!] =
    [expandTree 6 1792 fourRows49[0]!,
     expandTree 6 1792 fourRows49[1]!,
     expandTree 6 1792 fourRows49[2]!,
     expandTree 6 1792 fourRows49[3]!,
     expandTree 6 1792 fourRows49[4]!,
     expandTree 6 1792 fourRows49[5]!,
     expandTree 6 1792 fourRows49[6]!,
     expandTree 6 1792 fourRows49[7]!,
     expandTree 6 1792 fourRows49[8]!,
     expandTree 6 1792 fourRows49[9]!,
     expandTree 6 1792 fourRows49[10]!,
     expandTree 6 1792 fourRows49[11]!,
     expandTree 6 1792 fourRows49[12]!,
     expandTree 6 1792 fourRows49[13]!,
     expandTree 6 1792 fourRows49[14]!,
     expandTree 6 1792 fourRows49[15]!,
     expandTree 6 1792 fourRows49[16]!,
     expandTree 6 1792 fourRows49[17]!,
     expandTree 6 1792 fourRows49[18]!,
     expandTree 6 1792 fourRows49[19]!,
     expandTree 6 1792 fourRows49[20]!,
     expandTree 6 1792 fourRows49[21]!,
     expandTree 6 1792 fourRows49[22]!,
     expandTree 6 1792 fourRows49[23]!,
     expandTree 6 1792 fourRows49[24]!,
     expandTree 6 1792 fourRows49[25]!,
     expandTree 6 1792 fourRows49[26]!,
     expandTree 6 1792 fourRows49[27]!,
     expandTree 6 1792 fourRows49[28]!,
     expandTree 6 1792 fourRows49[29]!,
     expandTree 6 1792 fourRows49[30]!,
     expandTree 6 1792 fourRows49[31]!]
  rw [expanded49_row00, expanded49_row01, expanded49_row02, expanded49_row03, expanded49_row04, expanded49_row05, expanded49_row06, expanded49_row07, expanded49_row08, expanded49_row09, expanded49_row10, expanded49_row11, expanded49_row12, expanded49_row13, expanded49_row14, expanded49_row15, expanded49_row16, expanded49_row17, expanded49_row18, expanded49_row19, expanded49_row20, expanded49_row21, expanded49_row22, expanded49_row23, expanded49_row24, expanded49_row25, expanded49_row26, expanded49_row27, expanded49_row28, expanded49_row29, expanded49_row30, expanded49_row31]

set_option maxRecDepth 8192 in
private theorem expanded50_row00 : fourWide50[0]! =
    expandTree 6 1792 fourRows50[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row01 : fourWide50[1]! =
    expandTree 6 1792 fourRows50[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row02 : fourWide50[2]! =
    expandTree 6 1792 fourRows50[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row03 : fourWide50[3]! =
    expandTree 6 1792 fourRows50[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row04 : fourWide50[4]! =
    expandTree 6 1792 fourRows50[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row05 : fourWide50[5]! =
    expandTree 6 1792 fourRows50[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row06 : fourWide50[6]! =
    expandTree 6 1792 fourRows50[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row07 : fourWide50[7]! =
    expandTree 6 1792 fourRows50[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row08 : fourWide50[8]! =
    expandTree 6 1792 fourRows50[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row09 : fourWide50[9]! =
    expandTree 6 1792 fourRows50[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row10 : fourWide50[10]! =
    expandTree 6 1792 fourRows50[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row11 : fourWide50[11]! =
    expandTree 6 1792 fourRows50[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row12 : fourWide50[12]! =
    expandTree 6 1792 fourRows50[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row13 : fourWide50[13]! =
    expandTree 6 1792 fourRows50[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row14 : fourWide50[14]! =
    expandTree 6 1792 fourRows50[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row15 : fourWide50[15]! =
    expandTree 6 1792 fourRows50[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row16 : fourWide50[16]! =
    expandTree 6 1792 fourRows50[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row17 : fourWide50[17]! =
    expandTree 6 1792 fourRows50[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row18 : fourWide50[18]! =
    expandTree 6 1792 fourRows50[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row19 : fourWide50[19]! =
    expandTree 6 1792 fourRows50[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row20 : fourWide50[20]! =
    expandTree 6 1792 fourRows50[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row21 : fourWide50[21]! =
    expandTree 6 1792 fourRows50[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row22 : fourWide50[22]! =
    expandTree 6 1792 fourRows50[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row23 : fourWide50[23]! =
    expandTree 6 1792 fourRows50[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row24 : fourWide50[24]! =
    expandTree 6 1792 fourRows50[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row25 : fourWide50[25]! =
    expandTree 6 1792 fourRows50[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row26 : fourWide50[26]! =
    expandTree 6 1792 fourRows50[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row27 : fourWide50[27]! =
    expandTree 6 1792 fourRows50[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row28 : fourWide50[28]! =
    expandTree 6 1792 fourRows50[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row29 : fourWide50[29]! =
    expandTree 6 1792 fourRows50[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row30 : fourWide50[30]! =
    expandTree 6 1792 fourRows50[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded50_row31 : fourWide50[31]! =
    expandTree 6 1792 fourRows50[31]! := by decide +kernel

private theorem expanded50 : fourWide50 =
    fourRows50.map (expandTree 6 1792) := by
  change [fourWide50[0]!,
    fourWide50[1]!,
    fourWide50[2]!,
    fourWide50[3]!,
    fourWide50[4]!,
    fourWide50[5]!,
    fourWide50[6]!,
    fourWide50[7]!,
    fourWide50[8]!,
    fourWide50[9]!,
    fourWide50[10]!,
    fourWide50[11]!,
    fourWide50[12]!,
    fourWide50[13]!,
    fourWide50[14]!,
    fourWide50[15]!,
    fourWide50[16]!,
    fourWide50[17]!,
    fourWide50[18]!,
    fourWide50[19]!,
    fourWide50[20]!,
    fourWide50[21]!,
    fourWide50[22]!,
    fourWide50[23]!,
    fourWide50[24]!,
    fourWide50[25]!,
    fourWide50[26]!,
    fourWide50[27]!,
    fourWide50[28]!,
    fourWide50[29]!,
    fourWide50[30]!,
    fourWide50[31]!] =
    [expandTree 6 1792 fourRows50[0]!,
     expandTree 6 1792 fourRows50[1]!,
     expandTree 6 1792 fourRows50[2]!,
     expandTree 6 1792 fourRows50[3]!,
     expandTree 6 1792 fourRows50[4]!,
     expandTree 6 1792 fourRows50[5]!,
     expandTree 6 1792 fourRows50[6]!,
     expandTree 6 1792 fourRows50[7]!,
     expandTree 6 1792 fourRows50[8]!,
     expandTree 6 1792 fourRows50[9]!,
     expandTree 6 1792 fourRows50[10]!,
     expandTree 6 1792 fourRows50[11]!,
     expandTree 6 1792 fourRows50[12]!,
     expandTree 6 1792 fourRows50[13]!,
     expandTree 6 1792 fourRows50[14]!,
     expandTree 6 1792 fourRows50[15]!,
     expandTree 6 1792 fourRows50[16]!,
     expandTree 6 1792 fourRows50[17]!,
     expandTree 6 1792 fourRows50[18]!,
     expandTree 6 1792 fourRows50[19]!,
     expandTree 6 1792 fourRows50[20]!,
     expandTree 6 1792 fourRows50[21]!,
     expandTree 6 1792 fourRows50[22]!,
     expandTree 6 1792 fourRows50[23]!,
     expandTree 6 1792 fourRows50[24]!,
     expandTree 6 1792 fourRows50[25]!,
     expandTree 6 1792 fourRows50[26]!,
     expandTree 6 1792 fourRows50[27]!,
     expandTree 6 1792 fourRows50[28]!,
     expandTree 6 1792 fourRows50[29]!,
     expandTree 6 1792 fourRows50[30]!,
     expandTree 6 1792 fourRows50[31]!]
  rw [expanded50_row00, expanded50_row01, expanded50_row02, expanded50_row03, expanded50_row04, expanded50_row05, expanded50_row06, expanded50_row07, expanded50_row08, expanded50_row09, expanded50_row10, expanded50_row11, expanded50_row12, expanded50_row13, expanded50_row14, expanded50_row15, expanded50_row16, expanded50_row17, expanded50_row18, expanded50_row19, expanded50_row20, expanded50_row21, expanded50_row22, expanded50_row23, expanded50_row24, expanded50_row25, expanded50_row26, expanded50_row27, expanded50_row28, expanded50_row29, expanded50_row30, expanded50_row31]

set_option maxRecDepth 8192 in
private theorem expanded51_row00 : fourWide51[0]! =
    expandTree 6 1792 fourRows51[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row01 : fourWide51[1]! =
    expandTree 6 1792 fourRows51[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row02 : fourWide51[2]! =
    expandTree 6 1792 fourRows51[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row03 : fourWide51[3]! =
    expandTree 6 1792 fourRows51[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row04 : fourWide51[4]! =
    expandTree 6 1792 fourRows51[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row05 : fourWide51[5]! =
    expandTree 6 1792 fourRows51[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row06 : fourWide51[6]! =
    expandTree 6 1792 fourRows51[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row07 : fourWide51[7]! =
    expandTree 6 1792 fourRows51[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row08 : fourWide51[8]! =
    expandTree 6 1792 fourRows51[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row09 : fourWide51[9]! =
    expandTree 6 1792 fourRows51[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row10 : fourWide51[10]! =
    expandTree 6 1792 fourRows51[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row11 : fourWide51[11]! =
    expandTree 6 1792 fourRows51[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row12 : fourWide51[12]! =
    expandTree 6 1792 fourRows51[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row13 : fourWide51[13]! =
    expandTree 6 1792 fourRows51[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row14 : fourWide51[14]! =
    expandTree 6 1792 fourRows51[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row15 : fourWide51[15]! =
    expandTree 6 1792 fourRows51[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row16 : fourWide51[16]! =
    expandTree 6 1792 fourRows51[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row17 : fourWide51[17]! =
    expandTree 6 1792 fourRows51[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row18 : fourWide51[18]! =
    expandTree 6 1792 fourRows51[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row19 : fourWide51[19]! =
    expandTree 6 1792 fourRows51[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row20 : fourWide51[20]! =
    expandTree 6 1792 fourRows51[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row21 : fourWide51[21]! =
    expandTree 6 1792 fourRows51[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row22 : fourWide51[22]! =
    expandTree 6 1792 fourRows51[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row23 : fourWide51[23]! =
    expandTree 6 1792 fourRows51[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row24 : fourWide51[24]! =
    expandTree 6 1792 fourRows51[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row25 : fourWide51[25]! =
    expandTree 6 1792 fourRows51[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row26 : fourWide51[26]! =
    expandTree 6 1792 fourRows51[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row27 : fourWide51[27]! =
    expandTree 6 1792 fourRows51[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row28 : fourWide51[28]! =
    expandTree 6 1792 fourRows51[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row29 : fourWide51[29]! =
    expandTree 6 1792 fourRows51[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row30 : fourWide51[30]! =
    expandTree 6 1792 fourRows51[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded51_row31 : fourWide51[31]! =
    expandTree 6 1792 fourRows51[31]! := by decide +kernel

private theorem expanded51 : fourWide51 =
    fourRows51.map (expandTree 6 1792) := by
  change [fourWide51[0]!,
    fourWide51[1]!,
    fourWide51[2]!,
    fourWide51[3]!,
    fourWide51[4]!,
    fourWide51[5]!,
    fourWide51[6]!,
    fourWide51[7]!,
    fourWide51[8]!,
    fourWide51[9]!,
    fourWide51[10]!,
    fourWide51[11]!,
    fourWide51[12]!,
    fourWide51[13]!,
    fourWide51[14]!,
    fourWide51[15]!,
    fourWide51[16]!,
    fourWide51[17]!,
    fourWide51[18]!,
    fourWide51[19]!,
    fourWide51[20]!,
    fourWide51[21]!,
    fourWide51[22]!,
    fourWide51[23]!,
    fourWide51[24]!,
    fourWide51[25]!,
    fourWide51[26]!,
    fourWide51[27]!,
    fourWide51[28]!,
    fourWide51[29]!,
    fourWide51[30]!,
    fourWide51[31]!] =
    [expandTree 6 1792 fourRows51[0]!,
     expandTree 6 1792 fourRows51[1]!,
     expandTree 6 1792 fourRows51[2]!,
     expandTree 6 1792 fourRows51[3]!,
     expandTree 6 1792 fourRows51[4]!,
     expandTree 6 1792 fourRows51[5]!,
     expandTree 6 1792 fourRows51[6]!,
     expandTree 6 1792 fourRows51[7]!,
     expandTree 6 1792 fourRows51[8]!,
     expandTree 6 1792 fourRows51[9]!,
     expandTree 6 1792 fourRows51[10]!,
     expandTree 6 1792 fourRows51[11]!,
     expandTree 6 1792 fourRows51[12]!,
     expandTree 6 1792 fourRows51[13]!,
     expandTree 6 1792 fourRows51[14]!,
     expandTree 6 1792 fourRows51[15]!,
     expandTree 6 1792 fourRows51[16]!,
     expandTree 6 1792 fourRows51[17]!,
     expandTree 6 1792 fourRows51[18]!,
     expandTree 6 1792 fourRows51[19]!,
     expandTree 6 1792 fourRows51[20]!,
     expandTree 6 1792 fourRows51[21]!,
     expandTree 6 1792 fourRows51[22]!,
     expandTree 6 1792 fourRows51[23]!,
     expandTree 6 1792 fourRows51[24]!,
     expandTree 6 1792 fourRows51[25]!,
     expandTree 6 1792 fourRows51[26]!,
     expandTree 6 1792 fourRows51[27]!,
     expandTree 6 1792 fourRows51[28]!,
     expandTree 6 1792 fourRows51[29]!,
     expandTree 6 1792 fourRows51[30]!,
     expandTree 6 1792 fourRows51[31]!]
  rw [expanded51_row00, expanded51_row01, expanded51_row02, expanded51_row03, expanded51_row04, expanded51_row05, expanded51_row06, expanded51_row07, expanded51_row08, expanded51_row09, expanded51_row10, expanded51_row11, expanded51_row12, expanded51_row13, expanded51_row14, expanded51_row15, expanded51_row16, expanded51_row17, expanded51_row18, expanded51_row19, expanded51_row20, expanded51_row21, expanded51_row22, expanded51_row23, expanded51_row24, expanded51_row25, expanded51_row26, expanded51_row27, expanded51_row28, expanded51_row29, expanded51_row30, expanded51_row31]

set_option maxRecDepth 8192 in
private theorem expanded52_row00 : fourWide52[0]! =
    expandTree 6 1792 fourRows52[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row01 : fourWide52[1]! =
    expandTree 6 1792 fourRows52[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row02 : fourWide52[2]! =
    expandTree 6 1792 fourRows52[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row03 : fourWide52[3]! =
    expandTree 6 1792 fourRows52[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row04 : fourWide52[4]! =
    expandTree 6 1792 fourRows52[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row05 : fourWide52[5]! =
    expandTree 6 1792 fourRows52[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row06 : fourWide52[6]! =
    expandTree 6 1792 fourRows52[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row07 : fourWide52[7]! =
    expandTree 6 1792 fourRows52[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row08 : fourWide52[8]! =
    expandTree 6 1792 fourRows52[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row09 : fourWide52[9]! =
    expandTree 6 1792 fourRows52[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row10 : fourWide52[10]! =
    expandTree 6 1792 fourRows52[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row11 : fourWide52[11]! =
    expandTree 6 1792 fourRows52[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row12 : fourWide52[12]! =
    expandTree 6 1792 fourRows52[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row13 : fourWide52[13]! =
    expandTree 6 1792 fourRows52[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row14 : fourWide52[14]! =
    expandTree 6 1792 fourRows52[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row15 : fourWide52[15]! =
    expandTree 6 1792 fourRows52[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row16 : fourWide52[16]! =
    expandTree 6 1792 fourRows52[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row17 : fourWide52[17]! =
    expandTree 6 1792 fourRows52[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row18 : fourWide52[18]! =
    expandTree 6 1792 fourRows52[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row19 : fourWide52[19]! =
    expandTree 6 1792 fourRows52[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row20 : fourWide52[20]! =
    expandTree 6 1792 fourRows52[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row21 : fourWide52[21]! =
    expandTree 6 1792 fourRows52[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row22 : fourWide52[22]! =
    expandTree 6 1792 fourRows52[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row23 : fourWide52[23]! =
    expandTree 6 1792 fourRows52[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row24 : fourWide52[24]! =
    expandTree 6 1792 fourRows52[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row25 : fourWide52[25]! =
    expandTree 6 1792 fourRows52[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row26 : fourWide52[26]! =
    expandTree 6 1792 fourRows52[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row27 : fourWide52[27]! =
    expandTree 6 1792 fourRows52[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row28 : fourWide52[28]! =
    expandTree 6 1792 fourRows52[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row29 : fourWide52[29]! =
    expandTree 6 1792 fourRows52[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row30 : fourWide52[30]! =
    expandTree 6 1792 fourRows52[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded52_row31 : fourWide52[31]! =
    expandTree 6 1792 fourRows52[31]! := by decide +kernel

private theorem expanded52 : fourWide52 =
    fourRows52.map (expandTree 6 1792) := by
  change [fourWide52[0]!,
    fourWide52[1]!,
    fourWide52[2]!,
    fourWide52[3]!,
    fourWide52[4]!,
    fourWide52[5]!,
    fourWide52[6]!,
    fourWide52[7]!,
    fourWide52[8]!,
    fourWide52[9]!,
    fourWide52[10]!,
    fourWide52[11]!,
    fourWide52[12]!,
    fourWide52[13]!,
    fourWide52[14]!,
    fourWide52[15]!,
    fourWide52[16]!,
    fourWide52[17]!,
    fourWide52[18]!,
    fourWide52[19]!,
    fourWide52[20]!,
    fourWide52[21]!,
    fourWide52[22]!,
    fourWide52[23]!,
    fourWide52[24]!,
    fourWide52[25]!,
    fourWide52[26]!,
    fourWide52[27]!,
    fourWide52[28]!,
    fourWide52[29]!,
    fourWide52[30]!,
    fourWide52[31]!] =
    [expandTree 6 1792 fourRows52[0]!,
     expandTree 6 1792 fourRows52[1]!,
     expandTree 6 1792 fourRows52[2]!,
     expandTree 6 1792 fourRows52[3]!,
     expandTree 6 1792 fourRows52[4]!,
     expandTree 6 1792 fourRows52[5]!,
     expandTree 6 1792 fourRows52[6]!,
     expandTree 6 1792 fourRows52[7]!,
     expandTree 6 1792 fourRows52[8]!,
     expandTree 6 1792 fourRows52[9]!,
     expandTree 6 1792 fourRows52[10]!,
     expandTree 6 1792 fourRows52[11]!,
     expandTree 6 1792 fourRows52[12]!,
     expandTree 6 1792 fourRows52[13]!,
     expandTree 6 1792 fourRows52[14]!,
     expandTree 6 1792 fourRows52[15]!,
     expandTree 6 1792 fourRows52[16]!,
     expandTree 6 1792 fourRows52[17]!,
     expandTree 6 1792 fourRows52[18]!,
     expandTree 6 1792 fourRows52[19]!,
     expandTree 6 1792 fourRows52[20]!,
     expandTree 6 1792 fourRows52[21]!,
     expandTree 6 1792 fourRows52[22]!,
     expandTree 6 1792 fourRows52[23]!,
     expandTree 6 1792 fourRows52[24]!,
     expandTree 6 1792 fourRows52[25]!,
     expandTree 6 1792 fourRows52[26]!,
     expandTree 6 1792 fourRows52[27]!,
     expandTree 6 1792 fourRows52[28]!,
     expandTree 6 1792 fourRows52[29]!,
     expandTree 6 1792 fourRows52[30]!,
     expandTree 6 1792 fourRows52[31]!]
  rw [expanded52_row00, expanded52_row01, expanded52_row02, expanded52_row03, expanded52_row04, expanded52_row05, expanded52_row06, expanded52_row07, expanded52_row08, expanded52_row09, expanded52_row10, expanded52_row11, expanded52_row12, expanded52_row13, expanded52_row14, expanded52_row15, expanded52_row16, expanded52_row17, expanded52_row18, expanded52_row19, expanded52_row20, expanded52_row21, expanded52_row22, expanded52_row23, expanded52_row24, expanded52_row25, expanded52_row26, expanded52_row27, expanded52_row28, expanded52_row29, expanded52_row30, expanded52_row31]

set_option maxRecDepth 8192 in
private theorem expanded53_row00 : fourWide53[0]! =
    expandTree 6 1792 fourRows53[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row01 : fourWide53[1]! =
    expandTree 6 1792 fourRows53[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row02 : fourWide53[2]! =
    expandTree 6 1792 fourRows53[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row03 : fourWide53[3]! =
    expandTree 6 1792 fourRows53[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row04 : fourWide53[4]! =
    expandTree 6 1792 fourRows53[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row05 : fourWide53[5]! =
    expandTree 6 1792 fourRows53[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row06 : fourWide53[6]! =
    expandTree 6 1792 fourRows53[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row07 : fourWide53[7]! =
    expandTree 6 1792 fourRows53[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row08 : fourWide53[8]! =
    expandTree 6 1792 fourRows53[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row09 : fourWide53[9]! =
    expandTree 6 1792 fourRows53[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row10 : fourWide53[10]! =
    expandTree 6 1792 fourRows53[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row11 : fourWide53[11]! =
    expandTree 6 1792 fourRows53[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row12 : fourWide53[12]! =
    expandTree 6 1792 fourRows53[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row13 : fourWide53[13]! =
    expandTree 6 1792 fourRows53[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row14 : fourWide53[14]! =
    expandTree 6 1792 fourRows53[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row15 : fourWide53[15]! =
    expandTree 6 1792 fourRows53[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row16 : fourWide53[16]! =
    expandTree 6 1792 fourRows53[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row17 : fourWide53[17]! =
    expandTree 6 1792 fourRows53[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row18 : fourWide53[18]! =
    expandTree 6 1792 fourRows53[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row19 : fourWide53[19]! =
    expandTree 6 1792 fourRows53[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row20 : fourWide53[20]! =
    expandTree 6 1792 fourRows53[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row21 : fourWide53[21]! =
    expandTree 6 1792 fourRows53[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row22 : fourWide53[22]! =
    expandTree 6 1792 fourRows53[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row23 : fourWide53[23]! =
    expandTree 6 1792 fourRows53[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row24 : fourWide53[24]! =
    expandTree 6 1792 fourRows53[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row25 : fourWide53[25]! =
    expandTree 6 1792 fourRows53[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row26 : fourWide53[26]! =
    expandTree 6 1792 fourRows53[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row27 : fourWide53[27]! =
    expandTree 6 1792 fourRows53[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row28 : fourWide53[28]! =
    expandTree 6 1792 fourRows53[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row29 : fourWide53[29]! =
    expandTree 6 1792 fourRows53[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row30 : fourWide53[30]! =
    expandTree 6 1792 fourRows53[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded53_row31 : fourWide53[31]! =
    expandTree 6 1792 fourRows53[31]! := by decide +kernel

private theorem expanded53 : fourWide53 =
    fourRows53.map (expandTree 6 1792) := by
  change [fourWide53[0]!,
    fourWide53[1]!,
    fourWide53[2]!,
    fourWide53[3]!,
    fourWide53[4]!,
    fourWide53[5]!,
    fourWide53[6]!,
    fourWide53[7]!,
    fourWide53[8]!,
    fourWide53[9]!,
    fourWide53[10]!,
    fourWide53[11]!,
    fourWide53[12]!,
    fourWide53[13]!,
    fourWide53[14]!,
    fourWide53[15]!,
    fourWide53[16]!,
    fourWide53[17]!,
    fourWide53[18]!,
    fourWide53[19]!,
    fourWide53[20]!,
    fourWide53[21]!,
    fourWide53[22]!,
    fourWide53[23]!,
    fourWide53[24]!,
    fourWide53[25]!,
    fourWide53[26]!,
    fourWide53[27]!,
    fourWide53[28]!,
    fourWide53[29]!,
    fourWide53[30]!,
    fourWide53[31]!] =
    [expandTree 6 1792 fourRows53[0]!,
     expandTree 6 1792 fourRows53[1]!,
     expandTree 6 1792 fourRows53[2]!,
     expandTree 6 1792 fourRows53[3]!,
     expandTree 6 1792 fourRows53[4]!,
     expandTree 6 1792 fourRows53[5]!,
     expandTree 6 1792 fourRows53[6]!,
     expandTree 6 1792 fourRows53[7]!,
     expandTree 6 1792 fourRows53[8]!,
     expandTree 6 1792 fourRows53[9]!,
     expandTree 6 1792 fourRows53[10]!,
     expandTree 6 1792 fourRows53[11]!,
     expandTree 6 1792 fourRows53[12]!,
     expandTree 6 1792 fourRows53[13]!,
     expandTree 6 1792 fourRows53[14]!,
     expandTree 6 1792 fourRows53[15]!,
     expandTree 6 1792 fourRows53[16]!,
     expandTree 6 1792 fourRows53[17]!,
     expandTree 6 1792 fourRows53[18]!,
     expandTree 6 1792 fourRows53[19]!,
     expandTree 6 1792 fourRows53[20]!,
     expandTree 6 1792 fourRows53[21]!,
     expandTree 6 1792 fourRows53[22]!,
     expandTree 6 1792 fourRows53[23]!,
     expandTree 6 1792 fourRows53[24]!,
     expandTree 6 1792 fourRows53[25]!,
     expandTree 6 1792 fourRows53[26]!,
     expandTree 6 1792 fourRows53[27]!,
     expandTree 6 1792 fourRows53[28]!,
     expandTree 6 1792 fourRows53[29]!,
     expandTree 6 1792 fourRows53[30]!,
     expandTree 6 1792 fourRows53[31]!]
  rw [expanded53_row00, expanded53_row01, expanded53_row02, expanded53_row03, expanded53_row04, expanded53_row05, expanded53_row06, expanded53_row07, expanded53_row08, expanded53_row09, expanded53_row10, expanded53_row11, expanded53_row12, expanded53_row13, expanded53_row14, expanded53_row15, expanded53_row16, expanded53_row17, expanded53_row18, expanded53_row19, expanded53_row20, expanded53_row21, expanded53_row22, expanded53_row23, expanded53_row24, expanded53_row25, expanded53_row26, expanded53_row27, expanded53_row28, expanded53_row29, expanded53_row30, expanded53_row31]

set_option maxRecDepth 8192 in
private theorem expanded54_row00 : fourWide54[0]! =
    expandTree 6 1792 fourRows54[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row01 : fourWide54[1]! =
    expandTree 6 1792 fourRows54[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row02 : fourWide54[2]! =
    expandTree 6 1792 fourRows54[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row03 : fourWide54[3]! =
    expandTree 6 1792 fourRows54[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row04 : fourWide54[4]! =
    expandTree 6 1792 fourRows54[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row05 : fourWide54[5]! =
    expandTree 6 1792 fourRows54[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row06 : fourWide54[6]! =
    expandTree 6 1792 fourRows54[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row07 : fourWide54[7]! =
    expandTree 6 1792 fourRows54[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row08 : fourWide54[8]! =
    expandTree 6 1792 fourRows54[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row09 : fourWide54[9]! =
    expandTree 6 1792 fourRows54[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row10 : fourWide54[10]! =
    expandTree 6 1792 fourRows54[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row11 : fourWide54[11]! =
    expandTree 6 1792 fourRows54[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row12 : fourWide54[12]! =
    expandTree 6 1792 fourRows54[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row13 : fourWide54[13]! =
    expandTree 6 1792 fourRows54[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row14 : fourWide54[14]! =
    expandTree 6 1792 fourRows54[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row15 : fourWide54[15]! =
    expandTree 6 1792 fourRows54[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row16 : fourWide54[16]! =
    expandTree 6 1792 fourRows54[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row17 : fourWide54[17]! =
    expandTree 6 1792 fourRows54[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row18 : fourWide54[18]! =
    expandTree 6 1792 fourRows54[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row19 : fourWide54[19]! =
    expandTree 6 1792 fourRows54[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row20 : fourWide54[20]! =
    expandTree 6 1792 fourRows54[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row21 : fourWide54[21]! =
    expandTree 6 1792 fourRows54[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row22 : fourWide54[22]! =
    expandTree 6 1792 fourRows54[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row23 : fourWide54[23]! =
    expandTree 6 1792 fourRows54[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row24 : fourWide54[24]! =
    expandTree 6 1792 fourRows54[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row25 : fourWide54[25]! =
    expandTree 6 1792 fourRows54[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row26 : fourWide54[26]! =
    expandTree 6 1792 fourRows54[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row27 : fourWide54[27]! =
    expandTree 6 1792 fourRows54[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row28 : fourWide54[28]! =
    expandTree 6 1792 fourRows54[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row29 : fourWide54[29]! =
    expandTree 6 1792 fourRows54[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row30 : fourWide54[30]! =
    expandTree 6 1792 fourRows54[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded54_row31 : fourWide54[31]! =
    expandTree 6 1792 fourRows54[31]! := by decide +kernel

private theorem expanded54 : fourWide54 =
    fourRows54.map (expandTree 6 1792) := by
  change [fourWide54[0]!,
    fourWide54[1]!,
    fourWide54[2]!,
    fourWide54[3]!,
    fourWide54[4]!,
    fourWide54[5]!,
    fourWide54[6]!,
    fourWide54[7]!,
    fourWide54[8]!,
    fourWide54[9]!,
    fourWide54[10]!,
    fourWide54[11]!,
    fourWide54[12]!,
    fourWide54[13]!,
    fourWide54[14]!,
    fourWide54[15]!,
    fourWide54[16]!,
    fourWide54[17]!,
    fourWide54[18]!,
    fourWide54[19]!,
    fourWide54[20]!,
    fourWide54[21]!,
    fourWide54[22]!,
    fourWide54[23]!,
    fourWide54[24]!,
    fourWide54[25]!,
    fourWide54[26]!,
    fourWide54[27]!,
    fourWide54[28]!,
    fourWide54[29]!,
    fourWide54[30]!,
    fourWide54[31]!] =
    [expandTree 6 1792 fourRows54[0]!,
     expandTree 6 1792 fourRows54[1]!,
     expandTree 6 1792 fourRows54[2]!,
     expandTree 6 1792 fourRows54[3]!,
     expandTree 6 1792 fourRows54[4]!,
     expandTree 6 1792 fourRows54[5]!,
     expandTree 6 1792 fourRows54[6]!,
     expandTree 6 1792 fourRows54[7]!,
     expandTree 6 1792 fourRows54[8]!,
     expandTree 6 1792 fourRows54[9]!,
     expandTree 6 1792 fourRows54[10]!,
     expandTree 6 1792 fourRows54[11]!,
     expandTree 6 1792 fourRows54[12]!,
     expandTree 6 1792 fourRows54[13]!,
     expandTree 6 1792 fourRows54[14]!,
     expandTree 6 1792 fourRows54[15]!,
     expandTree 6 1792 fourRows54[16]!,
     expandTree 6 1792 fourRows54[17]!,
     expandTree 6 1792 fourRows54[18]!,
     expandTree 6 1792 fourRows54[19]!,
     expandTree 6 1792 fourRows54[20]!,
     expandTree 6 1792 fourRows54[21]!,
     expandTree 6 1792 fourRows54[22]!,
     expandTree 6 1792 fourRows54[23]!,
     expandTree 6 1792 fourRows54[24]!,
     expandTree 6 1792 fourRows54[25]!,
     expandTree 6 1792 fourRows54[26]!,
     expandTree 6 1792 fourRows54[27]!,
     expandTree 6 1792 fourRows54[28]!,
     expandTree 6 1792 fourRows54[29]!,
     expandTree 6 1792 fourRows54[30]!,
     expandTree 6 1792 fourRows54[31]!]
  rw [expanded54_row00, expanded54_row01, expanded54_row02, expanded54_row03, expanded54_row04, expanded54_row05, expanded54_row06, expanded54_row07, expanded54_row08, expanded54_row09, expanded54_row10, expanded54_row11, expanded54_row12, expanded54_row13, expanded54_row14, expanded54_row15, expanded54_row16, expanded54_row17, expanded54_row18, expanded54_row19, expanded54_row20, expanded54_row21, expanded54_row22, expanded54_row23, expanded54_row24, expanded54_row25, expanded54_row26, expanded54_row27, expanded54_row28, expanded54_row29, expanded54_row30, expanded54_row31]

set_option maxRecDepth 8192 in
private theorem expanded55_row00 : fourWide55[0]! =
    expandTree 6 1792 fourRows55[0]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row01 : fourWide55[1]! =
    expandTree 6 1792 fourRows55[1]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row02 : fourWide55[2]! =
    expandTree 6 1792 fourRows55[2]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row03 : fourWide55[3]! =
    expandTree 6 1792 fourRows55[3]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row04 : fourWide55[4]! =
    expandTree 6 1792 fourRows55[4]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row05 : fourWide55[5]! =
    expandTree 6 1792 fourRows55[5]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row06 : fourWide55[6]! =
    expandTree 6 1792 fourRows55[6]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row07 : fourWide55[7]! =
    expandTree 6 1792 fourRows55[7]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row08 : fourWide55[8]! =
    expandTree 6 1792 fourRows55[8]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row09 : fourWide55[9]! =
    expandTree 6 1792 fourRows55[9]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row10 : fourWide55[10]! =
    expandTree 6 1792 fourRows55[10]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row11 : fourWide55[11]! =
    expandTree 6 1792 fourRows55[11]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row12 : fourWide55[12]! =
    expandTree 6 1792 fourRows55[12]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row13 : fourWide55[13]! =
    expandTree 6 1792 fourRows55[13]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row14 : fourWide55[14]! =
    expandTree 6 1792 fourRows55[14]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row15 : fourWide55[15]! =
    expandTree 6 1792 fourRows55[15]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row16 : fourWide55[16]! =
    expandTree 6 1792 fourRows55[16]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row17 : fourWide55[17]! =
    expandTree 6 1792 fourRows55[17]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row18 : fourWide55[18]! =
    expandTree 6 1792 fourRows55[18]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row19 : fourWide55[19]! =
    expandTree 6 1792 fourRows55[19]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row20 : fourWide55[20]! =
    expandTree 6 1792 fourRows55[20]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row21 : fourWide55[21]! =
    expandTree 6 1792 fourRows55[21]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row22 : fourWide55[22]! =
    expandTree 6 1792 fourRows55[22]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row23 : fourWide55[23]! =
    expandTree 6 1792 fourRows55[23]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row24 : fourWide55[24]! =
    expandTree 6 1792 fourRows55[24]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row25 : fourWide55[25]! =
    expandTree 6 1792 fourRows55[25]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row26 : fourWide55[26]! =
    expandTree 6 1792 fourRows55[26]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row27 : fourWide55[27]! =
    expandTree 6 1792 fourRows55[27]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row28 : fourWide55[28]! =
    expandTree 6 1792 fourRows55[28]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row29 : fourWide55[29]! =
    expandTree 6 1792 fourRows55[29]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row30 : fourWide55[30]! =
    expandTree 6 1792 fourRows55[30]! := by decide +kernel

set_option maxRecDepth 8192 in
private theorem expanded55_row31 : fourWide55[31]! =
    expandTree 6 1792 fourRows55[31]! := by decide +kernel

private theorem expanded55 : fourWide55 =
    fourRows55.map (expandTree 6 1792) := by
  change [fourWide55[0]!,
    fourWide55[1]!,
    fourWide55[2]!,
    fourWide55[3]!,
    fourWide55[4]!,
    fourWide55[5]!,
    fourWide55[6]!,
    fourWide55[7]!,
    fourWide55[8]!,
    fourWide55[9]!,
    fourWide55[10]!,
    fourWide55[11]!,
    fourWide55[12]!,
    fourWide55[13]!,
    fourWide55[14]!,
    fourWide55[15]!,
    fourWide55[16]!,
    fourWide55[17]!,
    fourWide55[18]!,
    fourWide55[19]!,
    fourWide55[20]!,
    fourWide55[21]!,
    fourWide55[22]!,
    fourWide55[23]!,
    fourWide55[24]!,
    fourWide55[25]!,
    fourWide55[26]!,
    fourWide55[27]!,
    fourWide55[28]!,
    fourWide55[29]!,
    fourWide55[30]!,
    fourWide55[31]!] =
    [expandTree 6 1792 fourRows55[0]!,
     expandTree 6 1792 fourRows55[1]!,
     expandTree 6 1792 fourRows55[2]!,
     expandTree 6 1792 fourRows55[3]!,
     expandTree 6 1792 fourRows55[4]!,
     expandTree 6 1792 fourRows55[5]!,
     expandTree 6 1792 fourRows55[6]!,
     expandTree 6 1792 fourRows55[7]!,
     expandTree 6 1792 fourRows55[8]!,
     expandTree 6 1792 fourRows55[9]!,
     expandTree 6 1792 fourRows55[10]!,
     expandTree 6 1792 fourRows55[11]!,
     expandTree 6 1792 fourRows55[12]!,
     expandTree 6 1792 fourRows55[13]!,
     expandTree 6 1792 fourRows55[14]!,
     expandTree 6 1792 fourRows55[15]!,
     expandTree 6 1792 fourRows55[16]!,
     expandTree 6 1792 fourRows55[17]!,
     expandTree 6 1792 fourRows55[18]!,
     expandTree 6 1792 fourRows55[19]!,
     expandTree 6 1792 fourRows55[20]!,
     expandTree 6 1792 fourRows55[21]!,
     expandTree 6 1792 fourRows55[22]!,
     expandTree 6 1792 fourRows55[23]!,
     expandTree 6 1792 fourRows55[24]!,
     expandTree 6 1792 fourRows55[25]!,
     expandTree 6 1792 fourRows55[26]!,
     expandTree 6 1792 fourRows55[27]!,
     expandTree 6 1792 fourRows55[28]!,
     expandTree 6 1792 fourRows55[29]!,
     expandTree 6 1792 fourRows55[30]!,
     expandTree 6 1792 fourRows55[31]!]
  rw [expanded55_row00, expanded55_row01, expanded55_row02, expanded55_row03, expanded55_row04, expanded55_row05, expanded55_row06, expanded55_row07, expanded55_row08, expanded55_row09, expanded55_row10, expanded55_row11, expanded55_row12, expanded55_row13, expanded55_row14, expanded55_row15, expanded55_row16, expanded55_row17, expanded55_row18, expanded55_row19, expanded55_row20, expanded55_row21, expanded55_row22, expanded55_row23, expanded55_row24, expanded55_row25, expanded55_row26, expanded55_row27, expanded55_row28, expanded55_row29, expanded55_row30, expanded55_row31]

theorem fourWide_eq :
    fourWide.flatten = fourRows.flatten.map (expand 1792) := by
  have h : fourWide.flatten = fourRows.flatten.map (expandTree 6 1792) := by
    simp only [fourWide, fourRows, List.map_flatten, List.map_cons, List.map_nil,
      expanded00, expanded01, expanded02, expanded03, expanded04, expanded05, expanded06, expanded07, expanded08, expanded09, expanded10, expanded11, expanded12, expanded13, expanded14, expanded15, expanded16, expanded17, expanded18, expanded19, expanded20, expanded21, expanded22, expanded23, expanded24, expanded25, expanded26, expanded27, expanded28, expanded29, expanded30, expanded31, expanded32, expanded33, expanded34, expanded35, expanded36, expanded37, expanded38, expanded39, expanded40, expanded41, expanded42, expanded43, expanded44, expanded45, expanded46, expanded47, expanded48, expanded49, expanded50, expanded51, expanded52, expanded53, expanded54, expanded55]
  have hf : expandTree 6 1792 = expand 1792 := funext (expandTree_eq 6 1792)
  simpa only [hf] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.FourPowers
