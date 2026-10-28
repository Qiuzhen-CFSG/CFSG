module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.Structure

/-!
# A concrete projective configuration for the core comparison

These definitions specify 231 scalar lines and label them by the unordered
pairs of a 22-point set. The vectors come from the short orbit of the literal
binary matrices. The labels were found by reconstructing the stars of its
size-40 orbital graph. The definitions alone assert neither invariance nor
faithfulness; those are separate proof obligations.

The original ATLAS inputs and attribution are in `../../LinearModel/source/`.
The reproducible candidate data are retained in `source/projective-certificate.json`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- Decode a binary row, with bit zero in coordinate zero. -/
def packedVector (n : ℕ) : Fin 12 → ZMod 2 :=
  fun j => if n.testBit j.val then 1 else 0

/-- Packed representatives of the 231 candidate scalar lines. -/
def projectiveRepresentative : Fin 231 → ℕ :=
  ![5, 10, 15, 20, 30, 33, 36, 43, 46, 49, 50, 52, 71, 73, 74, 79, 83, 86, 102, 123, 126, 132, 142, 143, 144, 151, 154, 160, 166, 170, 177, 187, 189, 193, 198, 199, 200, 207, 219, 227, 236, 243, 244, 262, 263, 266, 275, 284, 286, 306, 317, 318, 333, 336, 345, 346, 352, 363, 378, 379, 389, 401, 408, 417, 422, 426, 431, 448, 450, 455, 456, 461, 465, 470, 476, 481, 491, 505, 508, 520, 530, 532, 534, 539, 550, 553, 564, 575, 580, 603, 607, 609, 619, 621, 627, 645, 646, 664, 665, 684, 687, 696, 698, 720, 723, 730, 732, 736, 738, 744, 745, 759, 777, 784, 788, 789, 794, 799, 800, 810, 811, 814, 821, 826, 835, 838, 846, 848, 852, 868, 869, 873, 880, 893, 913, 914, 923, 929, 934, 939, 943, 945, 949, 959, 960, 963, 981, 990, 997, 998, 1010, 1028, 1030, 1048, 1083, 1091, 1097, 1160, 1174, 1181, 1183, 1186, 1193, 1195, 1206, 1221, 1223, 1229, 1232, 1240, 1252, 1286, 1296, 1325, 1337, 1344, 1366, 1374, 1386, 1398, 1406, 1431, 1442, 1443, 1463, 1486, 1488, 1489, 1497, 1509, 1528, 1546, 1556, 1577, 1589, 1618, 1658, 1678, 1680, 1683, 1708, 1729, 1730, 1738, 1749, 1763, 1782, 1801, 1803, 1821, 1846, 1860, 1868, 1872, 1874, 1906, 1912, 1925, 1926, 1968, 1969, 1992, 1994, 2005, 2006, 2014, 2038, 2044, 2045, 2046, 2047]

/-- The concrete row representing a candidate projective point. -/
def projectiveVector (i : Fin 231) : Fin 12 → ZMod 2 :=
  packedVector (projectiveRepresentative i)

/-- The three nonzero scalar multiples of a row under the operator J. -/
def scalarLine (v : Fin 12 → ZMod 2) : Set (Fin 12 → ZMod 2) :=
  {v, Matrix.vecMul v matrixJ, v + Matrix.vecMul v matrixJ}

/-- The two endpoint labels of each candidate projective point. -/
def projectiveEndpoints : Fin 231 → Fin 22 × Fin 22 :=
  ![(0, 8), (18, 21), (4, 10), (1, 14), (16, 17), (4, 18), (10, 21), (10, 18), (4, 21), (8, 9), (11, 13), (2, 8), (7, 14), (5, 11), (3, 8), (8, 15), (0, 14), (0, 12), (6, 20), (8, 11), (8, 19), (16, 21), (17, 21), (11, 14), (17, 18), (9, 12), (16, 18), (20, 21), (3, 9), (5, 21), (18, 19), (15, 18), (6, 11), (12, 13), (11, 20), (2, 10), (10, 14), (1, 19), (1, 6), (5, 10), (3, 10), (2, 13), (11, 15), (12, 20), (1, 3), (2, 14), (1, 4), (4, 6), (14, 19), (4, 5), (4, 7), (2, 15), (3, 14), (12, 18), (13, 14), (9, 18), (19, 20), (9, 13), (6, 7), (5, 18), (14, 15), (12, 14), (5, 13), (3, 6), (7, 20), (0, 13), (0, 19), (18, 20), (14, 16), (6, 12), (1, 17), (2, 9), (5, 19), (14, 17), (1, 16), (7, 18), (3, 18), (0, 2), (0, 9), (4, 17), (5, 12), (10, 15), (11, 17), (10, 13), (4, 20), (4, 13), (7, 19), (9, 10), (3, 12), (5, 15), (2, 11), (6, 18), (2, 18), (11, 16), (7, 16), (12, 19), (17, 20), (2, 17), (9, 11), (1, 2), (7, 15), (1, 5), (0, 6), (11, 18), (10, 12), (13, 18), (6, 10), (15, 20), (3, 11), (7, 13), (0, 16), (10, 16), (3, 7), (0, 18), (4, 12), (0, 21), (8, 18), (8, 21), (5, 20), (15, 19), (8, 16), (8, 14), (4, 16), (4, 14), (0, 3), (0, 20), (7, 17), (8, 17), (9, 19), (1, 8), (9, 15), (5, 14), (1, 13), (6, 14), (15, 21), (2, 7), (19, 21), (14, 18), (2, 6), (1, 18), (3, 16), (13, 16), (14, 21), (1, 21), (6, 17), (5, 9), (7, 12), (15, 17), (3, 19), (14, 20), (9, 14), (7, 9), (12, 17), (17, 19), (3, 5), (7, 21), (13, 21), (13, 17), (0, 17), (2, 3), (7, 8), (1, 9), (2, 19), (6, 8), (1, 20), (0, 4), (12, 21), (6, 21), (8, 20), (5, 7), (4, 8), (10, 19), (13, 20), (10, 11), (0, 7), (5, 17), (11, 12), (9, 17), (0, 1), (3, 20), (1, 7), (2, 12), (7, 11), (2, 5), (6, 19), (10, 17), (3, 17), (6, 13), (4, 11), (7, 10), (4, 9), (9, 16), (12, 16), (0, 5), (3, 15), (13, 19), (0, 15), (15, 16), (16, 20), (3, 13), (6, 9), (1, 15), (2, 4), (5, 6), (1, 12), (4, 19), (2, 20), (1, 11), (13, 15), (1, 10), (10, 20), (12, 15), (16, 19), (9, 20), (5, 16), (11, 21), (3, 21), (8, 12), (0, 11), (6, 15), (5, 8), (2, 16), (8, 13), (0, 10), (6, 16), (3, 4), (9, 21), (2, 21), (11, 19), (8, 10), (4, 15)]

/-- A matrix fixes every specified scalar line under its right row action. -/
def FixesCoreLines (u : Matrix12ˣ) : Prop :=
  ∀ i : Fin 231, Matrix.vecMul (projectiveVector i) (u : Matrix12) ∈
    scalarLine (projectiveVector i)

/-- The actual scalar word fixes every candidate line. -/
theorem scalarUnit_fixesCoreLines : FixesCoreLines scalarUnit := by
  intro i
  rw [coe_scalarUnit, Matrix.vecMul_add, Matrix.vecMul_one]
  exact Or.inr (Or.inr rfl)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
