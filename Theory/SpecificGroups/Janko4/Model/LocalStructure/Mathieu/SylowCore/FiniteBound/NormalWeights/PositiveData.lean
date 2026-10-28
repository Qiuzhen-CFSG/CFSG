module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Core

/-!
# Checked conjugates and cached row counts

These 22 representatives cover the positive nonidentity weights. For each,
`conjugatesN` lists conjugator/target pairs and `cachedRowsN` stores the exact
image rows of those targets. Each conjugacy, row identity, and finite count is
proved separately by kernel reduction. Normality will place the listed targets
in the subgroup; `Core.card_le_conjugate_rows` then applies the checked count.

The untrusted discovery and reproducibility instructions are in `source/`.
Source tables: the ATLAS max1 words in `QuotientInvolutions.SylowData` and the
basis pairs and pair labels in `Image.StarData`. The row action is unchanged.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

def representatives : Fin 22 → Index := ![(0, 0, 5), (0, 0, 6), (0, 1, 0), (0, 1, 2), (0, 2, 0), (0, 2, 6), (0, 5, 6), (0, 5, 7), (1, 3, 6), (1, 4, 1), (4, 0, 2), (4, 1, 0), (4, 3, 0), (4, 3, 7), (6, 0, 1), (6, 1, 5), (6, 2, 3), (6, 3, 3), (6, 5, 4), (14, 0, 7), (14, 5, 5), (14, 7, 7)]

def bounds : Fin 22 → ℕ := ![8, 2, 16, 8, 2, 32, 16, 8, 64, 8, 8, 128, 2, 8, 64, 8, 16, 16, 8, 16, 32, 64]

def conjugates0 : List (Index × Index) := [((0, 0, 0), (0, 0, 5)), ((0, 1, 0), (0, 2, 7)), ((1, 0, 0), (14, 5, 0)), ((1, 1, 0), (15, 6, 1))]

def cachedRows0 : List (Fin 11 → ℕ) := [
  ![1, 581, 413, 89, 974, 302, 926, 128, 655, 512, 1865],
  ![1186, 1838, 41, 1158, 946, 32, 1927, 70, 655, 1637, 1865],
  ![1467, 184, 120, 1041, 1388, 313, 64, 70, 1503, 1978, 223],
  ![2044, 184, 374, 116, 1763, 1557, 392, 128, 180, 1339, 1394]]

theorem conjugates0_valid :
    ∀ c ∈ conjugates0, Conjugates (representatives 0) c.1 c.2 := by
  have h : conjugates0.all (fun c => decide (Conjugates (representatives 0) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows0_valid :
    conjugates0.map (fun c => rows c.2) = cachedRows0 := by decide +kernel

theorem cachedRows0_count :
    Fintype.card (RowSolutions cachedRows0) = bounds 0 := by decide +kernel

def conjugates1 : List (Index × Index) := [((0, 0, 0), (0, 0, 6)), ((0, 1, 0), (0, 7, 6)), ((0, 0, 1), (0, 0, 7)), ((0, 1, 1), (0, 5, 5)), ((1, 0, 0), (4, 6, 1)), ((1, 0, 1), (15, 4, 1))]

def cachedRows1 : List (Fin 11 → ℕ) := [
  ![1, 1534, 924, 227, 1714, 851, 1572, 128, 1865, 512, 655],
  ![71, 1410, 147, 31, 1345, 32, 1367, 128, 1024, 640, 256],
  ![1, 1977, 517, 116, 1388, 667, 1530, 128, 1024, 512, 256],
  ![1058, 686, 120, 1169, 1763, 32, 598, 70, 1865, 1571, 655],
  ![1637, 47, 41, 165, 1714, 1732, 64, 128, 429, 1186, 1131],
  ![991, 83, 147, 1212, 974, 1819, 64, 70, 1394, 280, 180]]

theorem conjugates1_valid :
    ∀ c ∈ conjugates1, Conjugates (representatives 1) c.1 c.2 := by
  have h : conjugates1.all (fun c => decide (Conjugates (representatives 1) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows1_valid :
    conjugates1.map (fun c => rows c.2) = cachedRows1 := by decide +kernel

theorem cachedRows1_count :
    Fintype.card (RowSolutions cachedRows1) = bounds 1 := by decide +kernel

def conjugates2 : List (Index × Index) := [((0, 0, 0), (0, 1, 0)), ((0, 0, 1), (0, 4, 1)), ((0, 0, 3), (0, 3, 6))]

def cachedRows2 : List (Fin 11 → ℕ) := [
  ![898, 2, 8, 4, 16, 991, 959, 883, 1131, 1819, 740],
  ![586, 1385, 1041, 374, 170, 1978, 523, 949, 1131, 1557, 740],
  ![313, 1491, 1261, 633, 857, 2044, 589, 949, 2020, 1440, 429]]

theorem conjugates2_valid :
    ∀ c ∈ conjugates2, Conjugates (representatives 2) c.1 c.2 := by
  have h : conjugates2.all (fun c => decide (Conjugates (representatives 2) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows2_valid :
    conjugates2.map (fun c => rows c.2) = cachedRows2 := by decide +kernel

theorem cachedRows2_count :
    Fintype.card (RowSolutions cachedRows2) = bounds 2 := by decide +kernel

def conjugates3 : List (Index × Index) := [((0, 0, 0), (0, 1, 2)), ((1, 0, 0), (10, 6, 1)), ((0, 0, 1), (0, 4, 5)), ((1, 0, 1), (11, 1, 6))]

def cachedRows3 : List (Fin 11 → ℕ) := [
  ![898, 1385, 831, 819, 168, 350, 1261, 637, 256, 1557, 1024],
  ![766, 2, 116, 120, 164, 735, 523, 699, 1131, 708, 848],
  ![586, 2, 589, 1834, 1401, 1339, 50, 699, 256, 1819, 1024],
  ![127, 2, 1041, 374, 1670, 1333, 1704, 637, 256, 131, 1789]]

theorem conjugates3_valid :
    ∀ c ∈ conjugates3, Conjugates (representatives 3) c.1 c.2 := by
  have h : conjugates3.all (fun c => decide (Conjugates (representatives 3) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows3_valid :
    conjugates3.map (fun c => rows c.2) = cachedRows3 := by decide +kernel

theorem cachedRows3_count :
    Fintype.card (RowSolutions cachedRows3) = bounds 3 := by decide +kernel

def conjugates4 : List (Index × Index) := [((0, 0, 0), (0, 2, 0)), ((0, 0, 1), (0, 2, 5)), ((0, 1, 0), (0, 5, 0)), ((0, 1, 1), (0, 7, 7)), ((1, 0, 1), (14, 0, 0)), ((1, 1, 1), (15, 3, 6))]

def cachedRows4 : List (Fin 11 → ℕ) := [
  ![1186, 83, 750, 1084, 1742, 667, 573, 70, 1865, 1637, 655],
  ![1186, 532, 945, 1133, 1494, 851, 293, 70, 1024, 1637, 256],
  ![1058, 47, 295, 1030, 1341, 302, 392, 70, 1024, 1571, 256],
  ![71, 1795, 266, 78, 1625, 302, 1615, 128, 1865, 640, 655],
  ![350, 83, 413, 31, 135, 55, 392, 128, 223, 863, 1503],
  ![863, 47, 924, 1158, 251, 1128, 819, 70, 1789, 350, 1021]]

theorem conjugates4_valid :
    ∀ c ∈ conjugates4, Conjugates (representatives 4) c.1 c.2 := by
  have h : conjugates4.all (fun c => decide (Conjugates (representatives 4) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows4_valid :
    conjugates4.map (fun c => rows c.2) = cachedRows4 := by decide +kernel

theorem cachedRows4_count :
    Fintype.card (RowSolutions cachedRows4) = bounds 4 := by decide +kernel

def conjugates5 : List (Index × Index) := [((0, 0, 0), (0, 2, 6)), ((1, 0, 0), (4, 4, 1))]

def cachedRows5 : List (Fin 11 → ℕ) := [
  ![1186, 1385, 374, 1041, 170, 302, 1183, 70, 256, 1637, 1024],
  ![640, 2, 266, 1133, 857, 1994, 392, 70, 1131, 71, 429]]

theorem conjugates5_valid :
    ∀ c ∈ conjugates5, Conjugates (representatives 5) c.1 c.2 := by
  have h : conjugates5.all (fun c => decide (Conjugates (representatives 5) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows5_valid :
    conjugates5.map (fun c => rows c.2) = cachedRows5 := by decide +kernel

theorem cachedRows5_count :
    Fintype.card (RowSolutions cachedRows5) = bounds 5 := by decide +kernel

def conjugates6 : List (Index × Index) := [((0, 0, 0), (0, 5, 6)), ((0, 0, 1), (0, 7, 0)), ((1, 0, 0), (4, 3, 6))]

def cachedRows6 : List (Fin 11 → ℕ) := [
  ![1058, 1491, 633, 1261, 857, 667, 1834, 70, 655, 1571, 1865],
  ![71, 184, 973, 50, 995, 851, 819, 128, 655, 640, 1865],
  ![512, 184, 517, 1169, 170, 1151, 573, 70, 2020, 1, 740]]

theorem conjugates6_valid :
    ∀ c ∈ conjugates6, Conjugates (representatives 6) c.1 c.2 := by
  have h : conjugates6.all (fun c => decide (Conjugates (representatives 6) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows6_valid :
    conjugates6.map (fun c => rows c.2) = cachedRows6 := by decide +kernel

theorem cachedRows6_count :
    Fintype.card (RowSolutions cachedRows6) = bounds 6 := by decide +kernel

def conjugates7 : List (Index × Index) := [((0, 0, 0), (0, 5, 7)), ((1, 0, 0), (15, 1, 6)), ((0, 0, 1), (0, 7, 5)), ((1, 0, 1), (14, 2, 0))]

def cachedRows7 : List (Fin 11 → ℕ) := [
  ![1058, 1874, 806, 1212, 135, 851, 1268, 70, 256, 1571, 1024],
  ![1978, 2, 633, 78, 1494, 1440, 573, 128, 1021, 1467, 1789],
  ![71, 569, 596, 165, 251, 667, 43, 128, 256, 640, 1024],
  ![1339, 2, 945, 1261, 1625, 586, 819, 70, 1686, 2044, 848]]

theorem conjugates7_valid :
    ∀ c ∈ conjugates7, Conjugates (representatives 7) c.1 c.2 := by
  have h : conjugates7.all (fun c => decide (Conjugates (representatives 7) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows7_valid :
    conjugates7.map (fun c => rows c.2) = cachedRows7 := by decide +kernel

theorem cachedRows7_count :
    Fintype.card (RowSolutions cachedRows7) = bounds 7 := by decide +kernel

def conjugates8 : List (Index × Index) := [((0, 0, 0), (1, 3, 6)), ((0, 0, 1), (3, 3, 3))]

def cachedRows8 : List (Fin 11 → ℕ) := [
  ![1820, 2020, 970, 243, 1341, 293, 1128, 128, 1491, 1576, 1534],
  ![31, 180, 1994, 350, 1598, 374, 1848, 128, 1838, 1158, 1534]]

theorem conjugates8_valid :
    ∀ c ∈ conjugates8, Conjugates (representatives 8) c.1 c.2 := by
  have h : conjugates8.all (fun c => decide (Conjugates (representatives 8) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows8_valid :
    conjugates8.map (fun c => rows c.2) = cachedRows8 := by decide +kernel

theorem cachedRows8_count :
    Fintype.card (RowSolutions cachedRows8) = bounds 8 := by decide +kernel

def conjugates9 : List (Index × Index) := [((0, 0, 0), (1, 4, 1)), ((0, 0, 1), (3, 4, 0)), ((0, 0, 2), (7, 1, 4))]

def cachedRows9 : List (Fin 11 → ℕ) := [
  ![1882, 1131, 822, 1020, 1742, 598, 1819, 128, 1385, 1704, 1410],
  ![1084, 1021, 1463, 1467, 1007, 973, 1738, 70, 569, 165, 47],
  ![1133, 1131, 1128, 1186, 1527, 924, 131, 70, 1385, 50, 1977]]

theorem conjugates9_valid :
    ∀ c ∈ conjugates9, Conjugates (representatives 9) c.1 c.2 := by
  have h : conjugates9.all (fun c => decide (Conjugates (representatives 9) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows9_valid :
    conjugates9.map (fun c => rows c.2) = cachedRows9 := by decide +kernel

theorem cachedRows9_count :
    Fintype.card (RowSolutions cachedRows9) = bounds 9 := by decide +kernel

def conjugates10 : List (Index × Index) := [((0, 0, 0), (4, 0, 2)), ((1, 0, 3), (8, 5, 6))]

def cachedRows10 : List (Fin 11 → ℕ) := [
  ![1440, 2, 1576, 1572, 1584, 1978, 1169, 637, 1131, 55, 429],
  ![1099, 1385, 1261, 945, 2019, 1020, 831, 637, 1686, 1207, 429]]

theorem conjugates10_valid :
    ∀ c ∈ conjugates10, Conjugates (representatives 10) c.1 c.2 := by
  have h : conjugates10.all (fun c => decide (Conjugates (representatives 10) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows10_valid :
    conjugates10.map (fun c => rows c.2) = cachedRows10 := by decide +kernel

theorem cachedRows10_count :
    Fintype.card (RowSolutions cachedRows10) = bounds 10 := by decide +kernel

def conjugates11 : List (Index × Index) := [((0, 0, 0), (4, 1, 0))]

def cachedRows11 : List (Fin 11 → ℕ) := [
  ![1571, 1385, 120, 116, 995, 1732, 1367, 128, 1131, 1058, 429]]

theorem conjugates11_valid :
    ∀ c ∈ conjugates11, Conjugates (representatives 11) c.1 c.2 := by
  have h : conjugates11.all (fun c => decide (Conjugates (representatives 11) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows11_valid :
    conjugates11.map (fun c => rows c.2) = cachedRows11 := by decide +kernel

theorem cachedRows11_count :
    Fintype.card (RowSolutions cachedRows11) = bounds 11 := by decide +kernel

def conjugates12 : List (Index × Index) := [((0, 0, 0), (4, 3, 0)), ((0, 0, 1), (4, 6, 2)), ((0, 1, 0), (4, 4, 4)), ((0, 1, 1), (4, 4, 3)), ((1, 0, 1), (14, 5, 6)), ((1, 1, 1), (15, 1, 0))]

def cachedRows12 : List (Fin 11 → ℕ) := [
  ![512, 1410, 413, 1212, 1742, 1994, 1183, 70, 429, 1, 1131],
  ![1637, 686, 374, 50, 1388, 1994, 926, 128, 740, 1186, 2020],
  ![640, 1534, 596, 1158, 1341, 1151, 1834, 70, 740, 71, 2020],
  ![640, 1977, 973, 1041, 1763, 1463, 1268, 70, 429, 71, 1131],
  ![1467, 1410, 806, 1084, 974, 586, 1572, 70, 848, 1978, 1686],
  ![1978, 1534, 295, 165, 946, 1557, 1183, 128, 1394, 1467, 180]]

theorem conjugates12_valid :
    ∀ c ∈ conjugates12, Conjugates (representatives 12) c.1 c.2 := by
  have h : conjugates12.all (fun c => decide (Conjugates (representatives 12) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows12_valid :
    conjugates12.map (fun c => rows c.2) = cachedRows12 := by decide +kernel

theorem cachedRows12_count :
    Fintype.card (RowSolutions cachedRows12) = bounds 12 := by decide +kernel

def conjugates13 : List (Index × Index) := [((0, 0, 0), (4, 3, 7)), ((0, 0, 1), (4, 6, 3)), ((1, 0, 0), (14, 0, 6)), ((1, 0, 1), (15, 4, 4))]

def cachedRows13 : List (Fin 11 → ℕ) := [
  ![512, 569, 924, 1030, 946, 1463, 293, 70, 1131, 1, 429],
  ![1637, 1874, 750, 31, 974, 1151, 1530, 128, 1131, 1186, 429],
  ![350, 1385, 517, 50, 1763, 898, 1834, 128, 1686, 863, 848],
  ![991, 1385, 973, 1169, 1388, 1128, 1572, 70, 1021, 280, 1789]]

theorem conjugates13_valid :
    ∀ c ∈ conjugates13, Conjugates (representatives 13) c.1 c.2 := by
  have h : conjugates13.all (fun c => decide (Conjugates (representatives 13) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows13_valid :
    conjugates13.map (fun c => rows c.2) = cachedRows13 := by decide +kernel

theorem cachedRows13_count :
    Fintype.card (RowSolutions cachedRows13) = bounds 13 := by decide +kernel

def conjugates14 : List (Index × Index) := [((0, 0, 0), (6, 0, 1)), ((0, 0, 2), (8, 1, 1))]

def cachedRows14 : List (Fin 11 → ℕ) := [
  ![1788, 1874, 1530, 91, 787, 397, 750, 128, 1021, 336, 1024],
  ![1395, 569, 43, 1418, 224, 708, 596, 128, 1686, 735, 429]]

theorem conjugates14_valid :
    ∀ c ∈ conjugates14, Conjugates (representatives 14) c.1 c.2 := by
  have h : conjugates14.all (fun c => decide (Conjugates (representatives 14) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows14_valid :
    conjugates14.map (fun c => rows c.2) = cachedRows14 := by decide +kernel

theorem cachedRows14_count :
    Fintype.card (RowSolutions cachedRows14) = bounds 14 := by decide +kernel

def conjugates15 : List (Index × Index) := [((0, 0, 0), (6, 1, 5)), ((0, 0, 3), (10, 1, 7))]

def cachedRows15 : List (Fin 11 → ℕ) := [
  ![1207, 1874, 227, 41, 298, 1174, 1484, 699, 1021, 1099, 1024],
  ![131, 569, 31, 750, 79, 607, 91, 699, 1131, 127, 848]]

theorem conjugates15_valid :
    ∀ c ∈ conjugates15, Conjugates (representatives 15) c.1 c.2 := by
  have h : conjugates15.all (fun c => decide (Conjugates (representatives 15) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows15_valid :
    conjugates15.map (fun c => rows c.2) = cachedRows15 := by decide +kernel

theorem cachedRows15_count :
    Fintype.card (RowSolutions cachedRows15) = bounds 15 := by decide +kernel

def conjugates16 : List (Index × Index) := [((0, 0, 0), (6, 2, 3)), ((0, 0, 3), (10, 0, 4))]

def cachedRows16 : List (Fin 11 → ℕ) := [
  ![607, 569, 293, 495, 1540, 131, 924, 70, 1021, 1333, 1024],
  ![1046, 1385, 1572, 1576, 28, 1738, 973, 70, 1131, 954, 848]]

theorem conjugates16_valid :
    ∀ c ∈ conjugates16, Conjugates (representatives 16) c.1 c.2 := by
  have h : conjugates16.all (fun c => decide (Conjugates (representatives 16) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows16_valid :
    conjugates16.map (fun c => rows c.2) = cachedRows16 := by decide +kernel

theorem cachedRows16_count :
    Fintype.card (RowSolutions cachedRows16) = bounds 16 := by decide +kernel

def conjugates17 : List (Index × Index) := [((0, 0, 0), (6, 3, 3)), ((0, 0, 3), (10, 6, 5))]

def cachedRows17 : List (Fin 11 → ℕ) := [
  ![1988, 1838, 1214, 1927, 1527, 1020, 227, 949, 180, 1776, 429],
  ![766, 1385, 1576, 1572, 28, 1333, 50, 949, 256, 970, 223]]

theorem conjugates17_valid :
    ∀ c ∈ conjugates17, Conjugates (representatives 17) c.1 c.2 := by
  have h : conjugates17.all (fun c => decide (Conjugates (representatives 17) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows17_valid :
    conjugates17.map (fun c => rows c.2) = cachedRows17 := by decide +kernel

theorem cachedRows17_count :
    Fintype.card (RowSolutions cachedRows17) = bounds 17 := by decide +kernel

def conjugates18 : List (Index × Index) := [((0, 0, 0), (6, 5, 4)), ((0, 0, 3), (10, 5, 1))]

def cachedRows18 : List (Fin 11 → ℕ) := [
  ![1722, 1385, 1367, 523, 261, 822, 120, 128, 1021, 464, 1024],
  ![1174, 1874, 1615, 1214, 522, 1207, 413, 70, 1131, 1020, 848]]

theorem conjugates18_valid :
    ∀ c ∈ conjugates18, Conjugates (representatives 18) c.1 c.2 := by
  have h : conjugates18.all (fun c => decide (Conjugates (representatives 18) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows18_valid :
    conjugates18.map (fun c => rows c.2) = cachedRows18 := by decide +kernel

theorem cachedRows18_count :
    Fintype.card (RowSolutions cachedRows18) = bounds 18 := by decide +kernel

def conjugates19 : List (Index × Index) := [((0, 0, 0), (14, 0, 7)), ((0, 0, 1), (15, 4, 3)), ((0, 1, 0), (15, 1, 7))]

def cachedRows19 : List (Fin 11 → ℕ) := [
  ![350, 1838, 924, 165, 1341, 586, 1268, 128, 1503, 863, 223],
  ![991, 1838, 596, 1030, 1714, 1440, 1530, 70, 180, 280, 1394],
  ![1978, 581, 806, 31, 1742, 1128, 293, 128, 180, 1467, 1394]]

theorem conjugates19_valid :
    ∀ c ∈ conjugates19, Conjugates (representatives 19) c.1 c.2 := by
  have h : conjugates19.all (fun c => decide (Conjugates (representatives 19) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows19_valid :
    conjugates19.map (fun c => rows c.2) = cachedRows19 := by decide +kernel

theorem cachedRows19_count :
    Fintype.card (RowSolutions cachedRows19) = bounds 19 := by decide +kernel

def conjugates20 : List (Index × Index) := [((0, 0, 0), (14, 5, 5)), ((0, 0, 1), (15, 3, 5))]

def cachedRows20 : List (Fin 11 → ℕ) := [
  ![1467, 569, 295, 1158, 1714, 55, 926, 70, 1686, 1978, 848],
  ![863, 1874, 413, 1084, 1345, 1557, 1615, 70, 1021, 350, 1789]]

theorem conjugates20_valid :
    ∀ c ∈ conjugates20, Conjugates (representatives 20) c.1 c.2 := by
  have h : conjugates20.all (fun c => decide (Conjugates (representatives 20) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows20_valid :
    conjugates20.map (fun c => rows c.2) = cachedRows20 := by decide +kernel

theorem cachedRows20_count :
    Fintype.card (RowSolutions cachedRows20) = bounds 20 := by decide +kernel

def conjugates21 : List (Index × Index) := [((0, 0, 0), (14, 7, 7)), ((0, 0, 1), (15, 6, 2))]

def cachedRows21 : List (Fin 11 → ℕ) := [
  ![280, 1874, 147, 89, 1742, 313, 1927, 128, 1686, 991, 848],
  ![2044, 569, 41, 227, 1341, 1819, 598, 128, 1021, 1339, 1789]]

theorem conjugates21_valid :
    ∀ c ∈ conjugates21, Conjugates (representatives 21) c.1 c.2 := by
  have h : conjugates21.all (fun c => decide (Conjugates (representatives 21) c.1 c.2)) = true :=
    by decide +kernel
  exact fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem cachedRows21_valid :
    conjugates21.map (fun c => rows c.2) = cachedRows21 := by decide +kernel

theorem cachedRows21_count :
    Fintype.card (RowSolutions cachedRows21) = bounds 21 := by decide +kernel

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
