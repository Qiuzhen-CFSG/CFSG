module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators

/-!
# Matrices of the literal Mathieu transversal words

The breadth-first words defining the point stabilizer's Schreier family are
computed by one binary matrix multiplication at each tree edge. The tables
also label the nineteen candidate Schreier matrices, including the identity;
their connection to the actual Schreier words is proved in `Edges.lean`.

The data is derived from `PointModel/source/model_diagnostic.py` and the
ATLAS-derived generator matrices of Wilson, Nickerson and Bray. Original
attribution, URLs and hashes remain in the J₄ `LinearModel/source/README.md`.
Source context: James (1973), Lemma 8.3; Aschbacher–Smith H.12.1,
printed pp.393–394. Every equality here is checked by the Lean kernel.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix
namespace SchreierCertificate
/-- Binary matrices for the breadth-first transversal. -/
def transversalMatrix : Fin 22 → Matrix12 :=
  ![fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412],
    fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    fromRows ![13, 2372, 3819, 1177, 2875, 3579, 2059, 3074, 3093, 208, 2544, 1875],
    fromRows ![3659, 280, 2372, 2875, 2687, 400, 2132, 1177, 13, 1446, 1499, 67],
    fromRows ![3151, 1848, 3311, 3339, 1869, 3220, 482, 2927, 3558, 1256, 3648, 3729],
    fromRows ![3074, 329, 350, 2671, 2930, 3819, 2860, 3661, 3124, 2179, 1804, 1799],
    fromRows ![2413, 181, 1073, 2963, 3062, 2948, 4047, 3661, 3248, 2179, 1007, 1787],
    fromRows ![128, 400, 280, 3659, 1559, 4, 28, 2875, 2687, 2, 31, 1499],
    fromRows ![122, 2948, 181, 2413, 3561, 3163, 3095, 2963, 3062, 412, 1579, 1007],
    fromRows ![1177, 3819, 329, 3074, 3093, 2372, 2048, 2671, 2930, 280, 1875, 1804],
    fromRows ![256, 4, 400, 128, 8, 1513, 1412, 3659, 1559, 1681, 3095, 31],
    fromRows ![2687, 280, 1875, 2875, 3659, 3976, 67, 2689, 1538, 3505, 987, 2132],
    fromRows ![2875, 2372, 2048, 1177, 13, 280, 1875, 225, 4014, 3976, 67, 2059],
    fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108],
    fromRows ![249, 3163, 2948, 122, 2891, 2408, 2307, 2413, 3561, 84, 3311, 1579],
    fromRows ![2875, 1875, 547, 2689, 1538, 280, 2372, 1774, 3477, 400, 2132, 2059],
    fromRows ![2891, 3163, 3095, 122, 249, 412, 1579, 409, 2613, 3964, 1108, 2307],
    fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64],
    fromRows ![409, 3220, 1848, 3151, 1944, 3095, 2901, 3339, 1869, 894, 1007, 3648],
    fromRows ![2689, 547, 3744, 1774, 3477, 1875, 712, 1016, 4051, 471, 2059, 268],
    fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499],
    fromRows ![122, 3095, 3220, 409, 2613, 3163, 2948, 3151, 1944, 2408, 2307, 1007]]
/-- The nineteen distinct matrices, including the identity. -/
def schreierMatrix : Fin 19 → Matrix12 :=
  ![fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    fromRows ![124, 3374, 2648, 271, 2891, 1578, 1591, 506, 1549, 1143, 3676, 2048],
    fromRows ![421, 3536, 388, 44, 351, 416, 3126, 292, 164, 3869, 2550, 1309],
    fromRows ![606, 547, 1282, 3521, 983, 690, 1512, 1561, 2550, 2065, 825, 1109],
    fromRows ![716, 3721, 31, 2666, 948, 191, 2048, 938, 8, 331, 953, 3095],
    fromRows ![1813, 3676, 3655, 21, 2394, 2734, 2771, 2574, 3226, 452, 3415, 330],
    fromRows ![2154, 1384, 1505, 556, 1525, 32, 2212, 2624, 1130, 2021, 3776, 4033],
    fromRows ![2190, 1525, 4060, 444, 833, 1362, 4075, 1635, 3881, 2960, 4072, 446],
    fromRows ![2429, 2960, 594, 3401, 833, 98, 695, 1490, 531, 2304, 1732, 2987],
    fromRows ![2445, 3453, 1011, 3612, 1533, 3344, 75, 2447, 2646, 2147, 21, 1787],
    fromRows ![2963, 1073, 1108, 3661, 3248, 181, 3468, 1793, 718, 3861, 1787, 1315],
    fromRows ![3005, 3006, 1362, 3150, 2304, 652, 3355, 1639, 2748, 3931, 1309, 2732],
    fromRows ![3050, 2, 3834, 1309, 3637, 1007, 911, 916, 1230, 1813, 2814, 1329],
    fromRows ![3086, 2510, 2553, 78, 3812, 1616, 2859, 3755, 1706, 75, 2682, 2874],
    fromRows ![3124, 350, 2315, 3661, 2671, 1759, 1067, 1152, 2280, 1714, 1900, 3336],
    fromRows ![3658, 1579, 870, 2559, 217, 2373, 3918, 2915, 2220, 2488, 2803, 2732],
    fromRows ![3719, 129, 2399, 2233, 984, 2492, 1791, 855, 3954, 3772, 4047, 837],
    fromRows ![3757, 3521, 3964, 3248, 1944, 3149, 2671, 2823, 3331, 2240, 2280, 3792],
    fromRows ![3934, 1012, 2610, 3622, 434, 2086, 2783, 2089, 3103, 2801, 323, 246]]
/-- Class of each of the forty-four literal Schreier words. -/
def schreierIndex : Fin 22 → Fin 2 → Fin 19 :=
  ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![3, 8], ![14, 1], ![10, 9], ![0, 18], ![0, 15], ![0, 16], ![0, 0], ![0, 0], ![13, 0], ![0, 17], ![0, 0], ![0, 2], ![0, 0], ![4, 0], ![0, 12], ![7, 5], ![0, 11], ![0, 6]]
def ambientMatrix : Fin 2 → Matrix12 := ![matrixA, matrixB]
lemma ambient_matrix (j : Fin 2) :
    ((ambientGenerator j : Matrix12ˣ) : Matrix12) = ambientMatrix j := by
  fin_cases j
  · exact coe_coreA
  · exact coe_coreB

set_option maxRecDepth 4000 in
lemma transversal_matrix (i : Fin 22) :
    ((transversal i : Matrix12ˣ) : Matrix12) = transversalMatrix i := by
  have t1 : ((transversal 1 : Matrix12ˣ) : Matrix12) = transversalMatrix 1 := by
    change (1 : Matrix12) = _
    decide +kernel
  have t0 : ((transversal 0 : Matrix12ˣ) : Matrix12) = transversalMatrix 0 := by
    have hw : transversal 0 = ambientGenerator 0 * transversal 1 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 1 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t1]
    decide +kernel
  have t17 : ((transversal 17 : Matrix12ˣ) : Matrix12) = transversalMatrix 17 := by
    have hw : transversal 17 = ambientGenerator 1 * transversal 1 := rfl
    rw [hw]
    change ((ambientGenerator 1 : Matrix12ˣ) : Matrix12) *
      ((transversal 1 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t1]
    decide +kernel
  have t20 : ((transversal 20 : Matrix12ˣ) : Matrix12) = transversalMatrix 20 := by
    have hw : transversal 20 = ambientGenerator 0 * transversal 0 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 0 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t0]
    decide +kernel
  have t10 : ((transversal 10 : Matrix12ˣ) : Matrix12) = transversalMatrix 10 := by
    have hw : transversal 10 = ambientGenerator 1 * transversal 0 := rfl
    rw [hw]
    change ((ambientGenerator 1 : Matrix12ˣ) : Matrix12) *
      ((transversal 0 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t0]
    decide +kernel
  have t13 : ((transversal 13 : Matrix12ˣ) : Matrix12) = transversalMatrix 13 := by
    have hw : transversal 13 = ambientGenerator 0 * transversal 20 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 20 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t20]
    decide +kernel
  have t7 : ((transversal 7 : Matrix12ˣ) : Matrix12) = transversalMatrix 7 := by
    have hw : transversal 7 = ambientGenerator 0 * transversal 10 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 10 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t10]
    decide +kernel
  have t16 : ((transversal 16 : Matrix12ˣ) : Matrix12) = transversalMatrix 16 := by
    have hw : transversal 16 = ambientGenerator 0 * transversal 13 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 13 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t13]
    decide +kernel
  have t3 : ((transversal 3 : Matrix12ˣ) : Matrix12) = transversalMatrix 3 := by
    have hw : transversal 3 = ambientGenerator 0 * transversal 7 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 7 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t7]
    decide +kernel
  have t21 : ((transversal 21 : Matrix12ˣ) : Matrix12) = transversalMatrix 21 := by
    have hw : transversal 21 = ambientGenerator 0 * transversal 16 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 16 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t16]
    decide +kernel
  have t14 : ((transversal 14 : Matrix12ˣ) : Matrix12) = transversalMatrix 14 := by
    have hw : transversal 14 = ambientGenerator 1 * transversal 16 := rfl
    rw [hw]
    change ((ambientGenerator 1 : Matrix12ˣ) : Matrix12) *
      ((transversal 16 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t16]
    decide +kernel
  have t12 : ((transversal 12 : Matrix12ˣ) : Matrix12) = transversalMatrix 12 := by
    have hw : transversal 12 = ambientGenerator 0 * transversal 3 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 3 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t3]
    decide +kernel
  have t11 : ((transversal 11 : Matrix12ˣ) : Matrix12) = transversalMatrix 11 := by
    have hw : transversal 11 = ambientGenerator 1 * transversal 3 := rfl
    rw [hw]
    change ((ambientGenerator 1 : Matrix12ˣ) : Matrix12) *
      ((transversal 3 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t3]
    decide +kernel
  have t18 : ((transversal 18 : Matrix12ˣ) : Matrix12) = transversalMatrix 18 := by
    have hw : transversal 18 = ambientGenerator 0 * transversal 21 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 21 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t21]
    decide +kernel
  have t8 : ((transversal 8 : Matrix12ˣ) : Matrix12) = transversalMatrix 8 := by
    have hw : transversal 8 = ambientGenerator 0 * transversal 14 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 14 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t14]
    decide +kernel
  have t2 : ((transversal 2 : Matrix12ˣ) : Matrix12) = transversalMatrix 2 := by
    have hw : transversal 2 = ambientGenerator 1 * transversal 12 := rfl
    rw [hw]
    change ((ambientGenerator 1 : Matrix12ˣ) : Matrix12) *
      ((transversal 12 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t12]
    decide +kernel
  have t15 : ((transversal 15 : Matrix12ˣ) : Matrix12) = transversalMatrix 15 := by
    have hw : transversal 15 = ambientGenerator 0 * transversal 11 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 11 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t11]
    decide +kernel
  have t4 : ((transversal 4 : Matrix12ˣ) : Matrix12) = transversalMatrix 4 := by
    have hw : transversal 4 = ambientGenerator 0 * transversal 18 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 18 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t18]
    decide +kernel
  have t6 : ((transversal 6 : Matrix12ˣ) : Matrix12) = transversalMatrix 6 := by
    have hw : transversal 6 = ambientGenerator 0 * transversal 8 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 8 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t8]
    decide +kernel
  have t9 : ((transversal 9 : Matrix12ˣ) : Matrix12) = transversalMatrix 9 := by
    have hw : transversal 9 = ambientGenerator 0 * transversal 2 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 2 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t2]
    decide +kernel
  have t19 : ((transversal 19 : Matrix12ˣ) : Matrix12) = transversalMatrix 19 := by
    have hw : transversal 19 = ambientGenerator 0 * transversal 15 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 15 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t15]
    decide +kernel
  have t5 : ((transversal 5 : Matrix12ˣ) : Matrix12) = transversalMatrix 5 := by
    have hw : transversal 5 = ambientGenerator 0 * transversal 9 := rfl
    rw [hw]
    change ((ambientGenerator 0 : Matrix12ˣ) : Matrix12) *
      ((transversal 9 : Matrix12ˣ) : Matrix12) = _
    rw [ambient_matrix, t9]
    decide +kernel
  fin_cases i
  · exact t0
  · exact t1
  · exact t2
  · exact t3
  · exact t4
  · exact t5
  · exact t6
  · exact t7
  · exact t8
  · exact t9
  · exact t10
  · exact t11
  · exact t12
  · exact t13
  · exact t14
  · exact t15
  · exact t16
  · exact t17
  · exact t18
  · exact t19
  · exact t20
  · exact t21

end SchreierCertificate
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
