module

public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Data.Fin.VecNotation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Tables

/-!
# The 24-point witness for the local conjugation image

The candidate tables come from the 24 stars in the graph on the 276-element
binary-coordinate orbit of the ATLAS local conjugation matrices. The graph
was used only to discover these data. The declarations below certify finite
identities directly; no graph reconstruction or external group computation
is trusted. Distinct vertices have a symmetric binary label, and all eleven
coordinate vectors occur among the labels.

`rightX` and `rightY` record right conjugation. Their inverse permutations
`starX` and `starY` are the proposed images for canonical left conjugation.
`StarGroup` is their generated subgroup; its order and its comparison with
the actual action image are separate obligations.

Source: `Scratch/J4LocalOrder/stars.py` and `stars.json` in the saved
local-order exploration (workspace `987246d9ba5a4fa9b3c370d659f2837b`),
using the ATLAS `J4G1-max1W1` local words and the certified `xMasks`, `yMasks`.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.Image

def rightXMap : Fin 24 → Fin 24 :=
  ![2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 12, 13, 10, 11, 15, 14, 22, 23, 19, 18, 21, 20, 16, 17]

def rightYMap : Fin 24 → Fin 24 :=
  ![5, 4, 1, 0, 2, 3, 8, 9, 10, 11, 6, 7, 16, 17, 18, 19, 22, 20, 23, 21, 13, 15, 12, 14]

def rightYInv : Fin 24 → Fin 24 :=
  ![3, 2, 4, 5, 1, 0, 10, 11, 6, 7, 8, 9, 22, 20, 23, 21, 12, 13, 14, 15, 17, 19, 16, 18]

def rightX : Equiv.Perm (Fin 24) where
  toFun := rightXMap
  invFun := rightXMap
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rightY : Equiv.Perm (Fin 24) where
  toFun := rightYMap
  invFun := rightYInv
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Left-conjugation convention. -/
def starX : Equiv.Perm (Fin 24) := rightX⁻¹

/-- Left-conjugation convention. -/
def starY : Equiv.Perm (Fin 24) := rightY⁻¹

def StarGroup : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure {starX, starY}

/-- Binary mask labeling an unordered pair; the diagonal has label zero. -/
def pairLabel : Fin 24 → Fin 24 → ℕ :=
  ![![0, 1, 28, 30, 55, 51, 71, 79, 180, 164, 281, 313, 522, 586, 898, 1021, 1058, 1186, 1394, 1485, 1789, 1570, 2045, 1821],
    ![1, 0, 29, 31, 54, 50, 70, 78, 181, 165, 280, 312, 523, 587, 899, 1020, 1059, 1187, 1395, 1484, 1788, 1571, 2044, 1820],
    ![28, 29, 0, 2, 43, 47, 91, 83, 168, 184, 261, 293, 534, 598, 926, 993, 1086, 1214, 1390, 1489, 1761, 1598, 2017, 1793],
    ![30, 31, 2, 0, 41, 45, 89, 81, 170, 186, 263, 295, 532, 596, 924, 995, 1084, 1212, 1388, 1491, 1763, 1596, 2019, 1795],
    ![55, 54, 43, 41, 0, 4, 112, 120, 131, 147, 302, 270, 573, 637, 949, 970, 1045, 1173, 1349, 1530, 1738, 1557, 1994, 1834],
    ![51, 50, 47, 45, 4, 0, 116, 124, 135, 151, 298, 266, 569, 633, 945, 974, 1041, 1169, 1345, 1534, 1742, 1553, 1998, 1838],
    ![71, 70, 91, 89, 112, 116, 0, 8, 243, 227, 350, 382, 589, 525, 965, 954, 1125, 1253, 1333, 1418, 1722, 1637, 1978, 1882],
    ![79, 78, 83, 81, 120, 124, 8, 0, 251, 235, 342, 374, 581, 517, 973, 946, 1133, 1261, 1341, 1410, 1714, 1645, 1970, 1874],
    ![180, 181, 168, 170, 131, 135, 243, 251, 0, 16, 429, 397, 702, 766, 822, 841, 1174, 1046, 1478, 1401, 1609, 1686, 1865, 1961],
    ![164, 165, 184, 186, 147, 151, 227, 235, 16, 0, 445, 413, 686, 750, 806, 857, 1158, 1030, 1494, 1385, 1625, 1670, 1881, 1977],
    ![281, 280, 261, 263, 302, 298, 350, 342, 429, 445, 0, 32, 787, 851, 667, 740, 1339, 1467, 1131, 1236, 2020, 1851, 1764, 1540],
    ![313, 312, 293, 295, 270, 266, 382, 374, 397, 413, 32, 0, 819, 883, 699, 708, 1307, 1435, 1099, 1268, 1988, 1819, 1732, 1572],
    ![522, 523, 534, 532, 573, 569, 589, 581, 702, 686, 787, 819, 0, 64, 392, 503, 1576, 1704, 1912, 1991, 1271, 1064, 1527, 1303],
    ![586, 587, 598, 596, 637, 633, 525, 517, 766, 750, 851, 883, 64, 0, 456, 439, 1640, 1768, 1848, 1927, 1207, 1128, 1463, 1367],
    ![898, 899, 926, 924, 949, 945, 965, 973, 822, 806, 667, 699, 392, 456, 0, 127, 1952, 1824, 1776, 1615, 1407, 1440, 1151, 1183],
    ![1021, 1020, 993, 995, 970, 974, 954, 946, 841, 857, 740, 708, 503, 439, 127, 0, 2015, 1887, 1679, 1584, 1280, 1503, 1024, 1248],
    ![1058, 1059, 1086, 1084, 1045, 1041, 1125, 1133, 1174, 1158, 1339, 1307, 1576, 1640, 1952, 2015, 0, 128, 336, 495, 735, 512, 991, 831],
    ![1186, 1187, 1214, 1212, 1173, 1169, 1253, 1261, 1046, 1030, 1467, 1435, 1704, 1768, 1824, 1887, 128, 0, 464, 367, 607, 640, 863, 959],
    ![1394, 1395, 1390, 1388, 1349, 1345, 1333, 1341, 1478, 1494, 1131, 1099, 1912, 1848, 1776, 1679, 336, 464, 0, 191, 911, 848, 655, 623],
    ![1485, 1484, 1489, 1491, 1530, 1534, 1418, 1410, 1401, 1385, 1236, 1268, 1991, 1927, 1615, 1584, 495, 367, 191, 0, 816, 1007, 560, 720],
    ![1789, 1788, 1761, 1763, 1738, 1742, 1722, 1714, 1609, 1625, 2020, 1988, 1271, 1207, 1407, 1280, 735, 607, 911, 816, 0, 223, 256, 480],
    ![1570, 1571, 1598, 1596, 1557, 1553, 1637, 1645, 1686, 1670, 1851, 1819, 1064, 1128, 1440, 1503, 512, 640, 848, 1007, 223, 0, 479, 319],
    ![2045, 2044, 2017, 2019, 1994, 1998, 1978, 1970, 1865, 1881, 1764, 1732, 1527, 1463, 1151, 1024, 991, 863, 655, 560, 256, 479, 0, 224],
    ![1821, 1820, 1793, 1795, 1834, 1838, 1882, 1874, 1961, 1977, 1540, 1572, 1303, 1367, 1183, 1248, 831, 959, 623, 720, 480, 319, 224, 0]]

theorem pairLabel_symm : ∀ i j, pairLabel i j = pairLabel j i := by decide +kernel

theorem pairLabel_lt : ∀ i j, pairLabel i j < 2048 := by decide +kernel

theorem pairLabel_eq_zero_iff : ∀ i j, pairLabel i j = 0 ↔ i = j := by decide +kernel

/-- Endpoints exhibiting every basis vector among the pair labels. -/
def basisPair : Fin 11 → Fin 24 × Fin 24 :=
  ![(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13),
    (16, 17), (20, 22), (16, 21), (15, 22)]

theorem pairLabel_basisPair :
    ∀ i, pairLabel (basisPair i).1 (basisPair i).2 = 2 ^ i.val := by decide +kernel

/-- XOR of the selected image masks, implementing a binary linear map. -/
def maskImage (masks : Fin 11 → ℕ) (v : ℕ) : ℕ :=
  (List.ofFn (fun i : Fin 11 => if v.testBit i.val then masks i else 0)).foldr Nat.xor 0

theorem pairLabel_rightX : ∀ i j,
    pairLabel (rightX i) (rightX j) = maskImage KernelCount.xMasks (pairLabel i j) := by
  decide +kernel

theorem pairLabel_rightY : ∀ i j,
    pairLabel (rightY i) (rightY j) = maskImage KernelCount.yMasks (pairLabel i j) := by
  decide +kernel

private theorem pairLabel_one_first : ∀ i j,
    pairLabel i j = 1 → i = 0 ∨ i = 1 := by decide +kernel

private theorem pairLabel_twentyEight_first : ∀ i j,
    pairLabel i j = 28 → i = 0 ∨ i = 2 := by decide +kernel

private theorem pairLabel_zero_injective : Function.Injective (pairLabel 0) := by
  decide +kernel

/-- A permutation fixing all pair labels fixes every star. This is the
faithfulness certificate for the star side of the action comparison. -/
theorem permutation_eq_one_of_pairLabel (p : Equiv.Perm (Fin 24))
    (h : ∀ i j, pairLabel (p i) (p j) = pairLabel i j) : p = 1 := by
  have h01 := pairLabel_one_first (p 0) (p 1) (h 0 1)
  have h02 := pairLabel_twentyEight_first (p 0) (p 2) (h 0 2)
  have hp0 : p 0 = 0 := by
    rcases h01 with h0 | h1
    · exact h0
    · rcases h02 with h0 | h2
      · exact h0
      · exact False.elim ((by decide : (1 : Fin 24) ≠ 2) (h1.symm.trans h2))
  apply Equiv.ext
  intro i
  apply pairLabel_zero_injective
  simpa only [hp0, Equiv.Perm.one_apply] using h 0 i

end Janko4.Cardinality.QuotientCount.Image
