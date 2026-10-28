module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions.FixedRank
import Mathlib.Tactic.FinCases
/-!
# Non-involution fixed-mask certificates

The 35 representatives are conjugacy representatives inside the actual star
Sylow subgroup. Their exact eleven rows fix at most sixteen of the 2048 masks.
Every row identity and count is kernel checked. The unchanged star and pair
labels come from the ATLAS max1 words and `Image.StarData`; the untrusted
witness generator is in `source/generate.py`.
-/
@[expose] public section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
open SylowCore SylowCore.FiniteBoundCertificate
open SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
def representatives : Fin 35 → Index := ![(0, 0, 3), (0, 1, 1), (0, 1, 3), (0, 1, 5), (0, 1, 6), (0, 5, 3), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 5), (1, 0, 6), (1, 0, 7), (1, 1, 0), (1, 1, 1), (1, 1, 3), (1, 1, 5), (1, 1, 7), (1, 2, 6), (1, 3, 0), (1, 3, 3), (1, 3, 7), (1, 4, 3), (1, 6, 4), (4, 0, 3), (6, 0, 2), (6, 0, 3), (6, 0, 5), (6, 1, 1), (6, 1, 2), (6, 1, 3), (6, 2, 1), (6, 3, 7), (6, 5, 3), (6, 5, 7), (14, 1, 7)]

def cachedRow0 : Fin 11 → ℕ := ![1, 532, 1615, 1086, 623, 1463, 120, 1253, 429, 1637, 2020]
def cachedRow1 : Fin 11 → ℕ := ![898, 581, 91, 1268, 1248, 1339, 165, 637, 655, 1557, 1865]
def cachedRow2 : Fin 11 → ℕ := ![898, 1795, 1484, 293, 1271, 1467, 116, 637, 1865, 1557, 655]
def cachedRow3 : Fin 11 → ℕ := ![898, 1838, 1158, 41, 946, 1978, 29, 883, 2020, 1819, 429]
def cachedRow4 : Fin 11 → ℕ := ![898, 1410, 31, 147, 1345, 863, 1576, 883, 429, 1819, 2020]
def cachedRow5 : Fin 11 → ℕ := ![1058, 569, 1927, 29, 1961, 1151, 413, 1253, 1131, 640, 740]
def cachedRow6 : Fin 11 → ℕ := ![1572, 180, 863, 667, 1645, 29, 336, 637, 1491, 64, 1534]
def cachedRow7 : Fin 11 → ℕ := ![1572, 1131, 1571, 898, 1998, 1214, 243, 637, 1385, 64, 1410]
def cachedRow8 : Fin 11 → ℕ := ![1572, 223, 1339, 1151, 164, 91, 1887, 637, 1534, 64, 1491]
def cachedRow9 : Fin 11 → ℕ := ![1572, 1503, 1395, 1207, 251, 367, 991, 949, 184, 392, 47]
def cachedRow10 : Fin 11 → ℕ := ![1572, 429, 735, 1848, 995, 1418, 1, 949, 47, 392, 184]
def cachedRow11 : Fin 11 → ℕ := ![1572, 1394, 954, 766, 1625, 495, 1467, 949, 83, 392, 2]
def cachedRow12 : Fin 11 → ℕ := ![831, 256, 439, 1046, 1345, 926, 55, 70, 1385, 523, 1410]
def cachedRow13 : Fin 11 → ℕ := ![831, 1503, 1463, 280, 79, 1615, 1099, 1253, 184, 1704, 47]
def cachedRow14 : Fin 11 → ℕ := ![831, 1789, 32, 2044, 1596, 1530, 766, 1253, 47, 1704, 184]
def cachedRow15 : Fin 11 → ℕ := ![831, 180, 1776, 607, 946, 598, 1732, 70, 1491, 523, 1534]
def cachedRow16 : Fin 11 → ℕ := ![831, 848, 131, 1887, 1763, 293, 851, 70, 1410, 523, 1385]
def cachedRow17 : Fin 11 → ℕ := ![1834, 1131, 1020, 822, 1742, 367, 1058, 883, 2, 64, 83]
def cachedRow18 : Fin 11 → ℕ := ![1820, 1024, 1407, 1333, 170, 598, 313, 128, 1410, 1576, 1385]
def cachedRow19 : Fin 11 → ℕ := ![1820, 1021, 302, 991, 1553, 1268, 1776, 1253, 2, 589, 83]
def cachedRow20 : Fin 11 → ℕ := ![1820, 1686, 1099, 1722, 974, 43, 667, 128, 1385, 1576, 1410]
def cachedRow21 : Fin 11 → ℕ := ![1882, 1789, 708, 181, 1388, 43, 1151, 128, 1410, 1704, 1385]
def cachedRow22 : Fin 11 → ℕ := ![959, 655, 397, 2015, 1714, 43, 898, 70, 1491, 589, 1534]
def cachedRow23 : Fin 11 → ℕ := ![1440, 686, 29, 1268, 623, 863, 8, 637, 740, 55, 2020]
def cachedRow24 : Fin 11 → ℕ := ![1788, 184, 819, 1882, 560, 131, 973, 128, 1503, 336, 740]
def cachedRow25 : Fin 11 → ℕ := ![1788, 532, 598, 1418, 319, 822, 4, 128, 1024, 336, 1021]
def cachedRow26 : Fin 11 → ℕ := ![1788, 569, 413, 1084, 342, 970, 1927, 1253, 1686, 1333, 1865]
def cachedRow27 : Fin 11 → ℕ := ![1207, 569, 495, 293, 1540, 954, 165, 949, 1686, 1349, 1865]
def cachedRow28 : Fin 11 → ℕ := ![1207, 184, 1882, 819, 560, 2015, 1169, 949, 180, 1349, 429]
def cachedRow29 : Fin 11 → ℕ := ![1207, 1795, 29, 1268, 522, 1887, 1133, 949, 1865, 1349, 1686]
def cachedRow30 : Fin 11 → ℕ := ![607, 1977, 1615, 1086, 1064, 766, 374, 70, 1024, 1333, 1021]
def cachedRow31 : Fin 11 → ℕ := ![1988, 581, 165, 924, 1998, 1046, 91, 637, 1503, 1848, 740]
def cachedRow32 : Fin 11 → ℕ := ![1722, 581, 926, 1484, 224, 766, 413, 128, 1503, 464, 740]
def cachedRow33 : Fin 11 → ℕ := ![1722, 1838, 750, 1212, 1970, 127, 293, 1059, 180, 1395, 429]
def cachedRow34 : Fin 11 → ℕ := ![851, 569, 1158, 295, 1714, 1637, 1484, 949, 1021, 1994, 1394]

def cachedRows : Fin 35 → Fin 11 → ℕ := ![cachedRow0, cachedRow1, cachedRow2, cachedRow3, cachedRow4, cachedRow5, cachedRow6, cachedRow7, cachedRow8, cachedRow9, cachedRow10, cachedRow11, cachedRow12, cachedRow13, cachedRow14, cachedRow15, cachedRow16, cachedRow17, cachedRow18, cachedRow19, cachedRow20, cachedRow21, cachedRow22, cachedRow23, cachedRow24, cachedRow25, cachedRow26, cachedRow27, cachedRow28, cachedRow29, cachedRow30, cachedRow31, cachedRow32, cachedRow33, cachedRow34]

theorem cachedRows_valid (k : Fin 35) : rows (representatives k) = cachedRows k := by
  fin_cases k <;> decide +kernel

private theorem zero0 : ZeroFixedTest cachedRow0 1665 = true := by decide +kernel
private theorem size0 : Fintype.card (CoordinateMasks 1665) ≤ 16 := by decide +kernel
private theorem bound0 : Nat.card {m : Fin 2048 // maskImage cachedRow0 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow0 1665 zero0 size0
private theorem zero1 : ZeroFixedTest cachedRow1 1920 = true := by decide +kernel
private theorem size1 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound1 : Nat.card {m : Fin 2048 // maskImage cachedRow1 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow1 1920 zero1 size1
private theorem zero2 : ZeroFixedTest cachedRow2 1472 = true := by decide +kernel
private theorem size2 : Fintype.card (CoordinateMasks 1472) ≤ 16 := by decide +kernel
private theorem bound2 : Nat.card {m : Fin 2048 // maskImage cachedRow2 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow2 1472 zero2 size2
private theorem zero3 : ZeroFixedTest cachedRow3 1680 = true := by decide +kernel
private theorem size3 : Fintype.card (CoordinateMasks 1680) ≤ 16 := by decide +kernel
private theorem bound3 : Nat.card {m : Fin 2048 // maskImage cachedRow3 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow3 1680 zero3 size3
private theorem zero4 : ZeroFixedTest cachedRow4 1920 = true := by decide +kernel
private theorem size4 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound4 : Nat.card {m : Fin 2048 // maskImage cachedRow4 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow4 1920 zero4 size4
private theorem zero5 : ZeroFixedTest cachedRow5 1728 = true := by decide +kernel
private theorem size5 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound5 : Nat.card {m : Fin 2048 // maskImage cachedRow5 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow5 1728 zero5 size5
private theorem zero6 : ZeroFixedTest cachedRow6 1920 = true := by decide +kernel
private theorem size6 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound6 : Nat.card {m : Fin 2048 // maskImage cachedRow6 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow6 1920 zero6 size6
private theorem zero7 : ZeroFixedTest cachedRow7 1920 = true := by decide +kernel
private theorem size7 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound7 : Nat.card {m : Fin 2048 // maskImage cachedRow7 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow7 1920 zero7 size7
private theorem zero8 : ZeroFixedTest cachedRow8 1920 = true := by decide +kernel
private theorem size8 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound8 : Nat.card {m : Fin 2048 // maskImage cachedRow8 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow8 1920 zero8 size8
private theorem zero9 : ZeroFixedTest cachedRow9 1920 = true := by decide +kernel
private theorem size9 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound9 : Nat.card {m : Fin 2048 // maskImage cachedRow9 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow9 1920 zero9 size9
private theorem zero10 : ZeroFixedTest cachedRow10 1728 = true := by decide +kernel
private theorem size10 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound10 : Nat.card {m : Fin 2048 // maskImage cachedRow10 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow10 1728 zero10 size10
private theorem zero11 : ZeroFixedTest cachedRow11 1696 = true := by decide +kernel
private theorem size11 : Fintype.card (CoordinateMasks 1696) ≤ 16 := by decide +kernel
private theorem bound11 : Nat.card {m : Fin 2048 // maskImage cachedRow11 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow11 1696 zero11 size11
private theorem zero12 : ZeroFixedTest cachedRow12 1920 = true := by decide +kernel
private theorem size12 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound12 : Nat.card {m : Fin 2048 // maskImage cachedRow12 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow12 1920 zero12 size12
private theorem zero13 : ZeroFixedTest cachedRow13 1920 = true := by decide +kernel
private theorem size13 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound13 : Nat.card {m : Fin 2048 // maskImage cachedRow13 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow13 1920 zero13 size13
private theorem zero14 : ZeroFixedTest cachedRow14 1920 = true := by decide +kernel
private theorem size14 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound14 : Nat.card {m : Fin 2048 // maskImage cachedRow14 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow14 1920 zero14 size14
private theorem zero15 : ZeroFixedTest cachedRow15 1920 = true := by decide +kernel
private theorem size15 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound15 : Nat.card {m : Fin 2048 // maskImage cachedRow15 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow15 1920 zero15 size15
private theorem zero16 : ZeroFixedTest cachedRow16 1920 = true := by decide +kernel
private theorem size16 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound16 : Nat.card {m : Fin 2048 // maskImage cachedRow16 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow16 1920 zero16 size16
private theorem zero17 : ZeroFixedTest cachedRow17 1696 = true := by decide +kernel
private theorem size17 : Fintype.card (CoordinateMasks 1696) ≤ 16 := by decide +kernel
private theorem bound17 : Nat.card {m : Fin 2048 // maskImage cachedRow17 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow17 1696 zero17 size17
private theorem zero18 : ZeroFixedTest cachedRow18 1728 = true := by decide +kernel
private theorem size18 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound18 : Nat.card {m : Fin 2048 // maskImage cachedRow18 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow18 1728 zero18 size18
private theorem zero19 : ZeroFixedTest cachedRow19 1440 = true := by decide +kernel
private theorem size19 : Fintype.card (CoordinateMasks 1440) ≤ 16 := by decide +kernel
private theorem bound19 : Nat.card {m : Fin 2048 // maskImage cachedRow19 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow19 1440 zero19 size19
private theorem zero20 : ZeroFixedTest cachedRow20 1472 = true := by decide +kernel
private theorem size20 : Fintype.card (CoordinateMasks 1472) ≤ 16 := by decide +kernel
private theorem bound20 : Nat.card {m : Fin 2048 // maskImage cachedRow20 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow20 1472 zero20 size20
private theorem zero21 : ZeroFixedTest cachedRow21 1472 = true := by decide +kernel
private theorem size21 : Fintype.card (CoordinateMasks 1472) ≤ 16 := by decide +kernel
private theorem bound21 : Nat.card {m : Fin 2048 // maskImage cachedRow21 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow21 1472 zero21 size21
private theorem zero22 : ZeroFixedTest cachedRow22 1920 = true := by decide +kernel
private theorem size22 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound22 : Nat.card {m : Fin 2048 // maskImage cachedRow22 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow22 1920 zero22 size22
private theorem zero23 : ZeroFixedTest cachedRow23 1920 = true := by decide +kernel
private theorem size23 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound23 : Nat.card {m : Fin 2048 // maskImage cachedRow23 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow23 1920 zero23 size23
private theorem zero24 : ZeroFixedTest cachedRow24 1472 = true := by decide +kernel
private theorem size24 : Fintype.card (CoordinateMasks 1472) ≤ 16 := by decide +kernel
private theorem bound24 : Nat.card {m : Fin 2048 // maskImage cachedRow24 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow24 1472 zero24 size24
private theorem zero25 : ZeroFixedTest cachedRow25 1728 = true := by decide +kernel
private theorem size25 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound25 : Nat.card {m : Fin 2048 // maskImage cachedRow25 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow25 1728 zero25 size25
private theorem zero26 : ZeroFixedTest cachedRow26 1920 = true := by decide +kernel
private theorem size26 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound26 : Nat.card {m : Fin 2048 // maskImage cachedRow26 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow26 1920 zero26 size26
private theorem zero27 : ZeroFixedTest cachedRow27 1920 = true := by decide +kernel
private theorem size27 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound27 : Nat.card {m : Fin 2048 // maskImage cachedRow27 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow27 1920 zero27 size27
private theorem zero28 : ZeroFixedTest cachedRow28 1920 = true := by decide +kernel
private theorem size28 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound28 : Nat.card {m : Fin 2048 // maskImage cachedRow28 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow28 1920 zero28 size28
private theorem zero29 : ZeroFixedTest cachedRow29 1920 = true := by decide +kernel
private theorem size29 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound29 : Nat.card {m : Fin 2048 // maskImage cachedRow29 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow29 1920 zero29 size29
private theorem zero30 : ZeroFixedTest cachedRow30 1920 = true := by decide +kernel
private theorem size30 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound30 : Nat.card {m : Fin 2048 // maskImage cachedRow30 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow30 1920 zero30 size30
private theorem zero31 : ZeroFixedTest cachedRow31 1728 = true := by decide +kernel
private theorem size31 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound31 : Nat.card {m : Fin 2048 // maskImage cachedRow31 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow31 1728 zero31 size31
private theorem zero32 : ZeroFixedTest cachedRow32 1728 = true := by decide +kernel
private theorem size32 : Fintype.card (CoordinateMasks 1728) ≤ 16 := by decide +kernel
private theorem bound32 : Nat.card {m : Fin 2048 // maskImage cachedRow32 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow32 1728 zero32 size32
private theorem zero33 : ZeroFixedTest cachedRow33 1920 = true := by decide +kernel
private theorem size33 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound33 : Nat.card {m : Fin 2048 // maskImage cachedRow33 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow33 1920 zero33 size33
private theorem zero34 : ZeroFixedTest cachedRow34 1920 = true := by decide +kernel
private theorem size34 : Fintype.card (CoordinateMasks 1920) ≤ 16 := by decide +kernel
private theorem bound34 : Nat.card {m : Fin 2048 // maskImage cachedRow34 m.val = m.val} ≤ 16 :=
  fixed_bound_of_coordinates cachedRow34 1920 zero34 size34

theorem representative_bounds (k : Fin 35) : Nat.card {m : Fin 2048 // maskImage (cachedRows k) m.val = m.val} ≤ 16 := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
  · exact bound29
  · exact bound30
  · exact bound31
  · exact bound32
  · exact bound33
  · exact bound34

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
