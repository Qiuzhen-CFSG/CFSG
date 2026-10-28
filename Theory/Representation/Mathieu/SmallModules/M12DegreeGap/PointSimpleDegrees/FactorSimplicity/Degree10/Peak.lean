module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Criterion

/-!
# Degree-10 low-rank operator for the M₁₁ coset factor

The packed columns use exactly `Data.modelMatrix`, acting on column vectors.
All finite identities are checked by the Lean kernel. The low-rank operator
and the orbit bases are reproduced by `../source/discover.py` and `export.py`.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10
open Matrix

def node0 : Fin 10 → ℕ := identity 10

def node1 : Fin 10 → ℕ := fun j => ((Data.modelColumns[1]!)[0]!)[j.val]!

def node2 : Fin 10 → ℕ := fun j => ((Data.modelColumns[1]!)[1]!)[j.val]!

def generators : Fin 2 → Fin 10 → ℕ := ![node1, node2]

theorem generators_eq (s : Fin 2) : matrix (m := 10) (generators s) = Data.modelMatrix 1 s := by
  fin_cases s <;> rfl

def node3 : Fin 10 → ℕ := fun j => (#[270, 455, 975, 366, 270, 455, 455, 423, 870, 366] : Array ℕ)[j.val]!

private theorem check3 : plus node0 node1 = node3 := by decide +kernel

def node4 : Fin 10 → ℕ := fun j => (#[769, 378, 44, 776, 735, 368, 291, 582, 677, 421] : Array ℕ)[j.val]!

private theorem check4 : product node0 node2 = node4 := by decide +kernel

def node5 : Fin 10 → ℕ := fun j => (#[1018, 749, 278, 928, 548, 743, 692, 386, 160, 269] : Array ℕ)[j.val]!

private theorem check5 : product node4 node1 = node5 := by decide +kernel

def node6 : Fin 10 → ℕ := fun j => (#[599, 922, 81, 525, 958, 727, 848, 66, 132, 297] : Array ℕ)[j.val]!

private theorem check6 : product node5 node2 = node6 := by decide +kernel

def node7 : Fin 10 → ℕ := fun j => (#[789, 400, 383, 712, 764, 221, 346, 975, 869, 492] : Array ℕ)[j.val]!

private theorem check7 : product node6 node1 = node7 := by decide +kernel

def node8 : Fin 10 → ℕ := fun j => (#[412, 838, 874, 65, 183, 30, 317, 89, 148, 541] : Array ℕ)[j.val]!

private theorem check8 : product node7 node2 = node8 := by decide +kernel

def node9 : Fin 10 → ℕ := fun j => (#[357, 774, 374, 411, 78, 94, 381, 314, 786, 967] : Array ℕ)[j.val]!

private theorem check9 : product node8 node1 = node9 := by decide +kernel

def node10 : Fin 10 → ℕ := fun j => (#[432, 226, 179, 334, 320, 639, 303, 202, 688, 613] : Array ℕ)[j.val]!

private theorem check10 : product node9 node2 = node10 := by decide +kernel

def node11 : Fin 10 → ℕ := fun j => (#[543, 598, 300, 433, 751, 203, 923, 302, 356, 666] : Array ℕ)[j.val]!

private theorem check11 : product node10 node1 = node11 := by decide +kernel

def node12 : Fin 10 → ℕ := fun j => (#[481, 828, 86, 591, 532, 219, 486, 635, 76, 946] : Array ℕ)[j.val]!

private theorem check12 : product node11 node2 = node12 := by decide +kernel

def node13 : Fin 10 → ℕ := fun j => (#[975, 96, 705, 705, 943, 201, 201, 455, 870, 673] : Array ℕ)[j.val]!

private theorem check13 : product node3 node12 = node13 := by decide +kernel

def node14 : Fin 10 → ℕ := fun j => (#[774, 774, 870, 774, 774, 774, 774, 774, 870, 774] : Array ℕ)[j.val]!

private theorem check14 : product node13 node3 = node14 := by decide +kernel

def node15 : Fin 10 → ℕ := fun j => (#[769, 378, 44, 776, 735, 368, 291, 582, 677, 421] : Array ℕ)[j.val]!

private theorem check15 : product node0 node2 = node15 := by decide +kernel

def node16 : Fin 10 → ℕ := fun j => (#[1, 603, 596, 8, 320, 41, 430, 464, 446, 702] : Array ℕ)[j.val]!

private theorem check16 : product node15 node2 = node16 := by decide +kernel

def node17 : Fin 10 → ℕ := fun j => (#[440, 917, 300, 54, 249, 487, 96, 409, 822, 640] : Array ℕ)[j.val]!

private theorem check17 : product node16 node1 = node17 := by decide +kernel

def node18 : Fin 10 → ℕ := fun j => (#[870, 0, 0, 96, 0, 774, 0, 870, 0, 0] : Array ℕ)[j.val]!

private theorem check18 : product node14 node17 = node18 := by decide +kernel

def node19 : Fin 10 → ℕ := fun j => (#[0, 0, 774, 0, 0, 0, 0, 0, 774, 0] : Array ℕ)[j.val]!

private theorem check19 : product node18 node14 = node19 := by decide +kernel

def peak : Matrix (Fin 10) (Fin 10) (ZMod 2) := matrix node19

theorem peak_preserves (U : Submodule (ZMod 2) (Fin 10 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s))) : Preserves U peak := by
  have h0 : Preserves U (matrix node0) := by
    rw [node0, matrix_identity]
    exact preserves_one U
  have h1 : Preserves U (matrix node1) := hA 0
  have h2 : Preserves U (matrix node2) := hA 1
  have h3 := preserves_packed_add node0 node1 node3 h0 h1 check3
  have h4 := preserves_packed_mul node0 node2 node4 h0 h2 check4
  have h5 := preserves_packed_mul node4 node1 node5 h4 h1 check5
  have h6 := preserves_packed_mul node5 node2 node6 h5 h2 check6
  have h7 := preserves_packed_mul node6 node1 node7 h6 h1 check7
  have h8 := preserves_packed_mul node7 node2 node8 h7 h2 check8
  have h9 := preserves_packed_mul node8 node1 node9 h8 h1 check9
  have h10 := preserves_packed_mul node9 node2 node10 h9 h2 check10
  have h11 := preserves_packed_mul node10 node1 node11 h10 h1 check11
  have h12 := preserves_packed_mul node11 node2 node12 h11 h2 check12
  have h13 := preserves_packed_mul node3 node12 node13 h3 h12 check13
  have h14 := preserves_packed_mul node13 node3 node14 h13 h3 check14
  have h15 := preserves_packed_mul node0 node2 node15 h0 h2 check15
  have h16 := preserves_packed_mul node15 node2 node16 h15 h2 check16
  have h17 := preserves_packed_mul node16 node1 node17 h16 h1 check17
  have h18 := preserves_packed_mul node14 node17 node18 h14 h17 check18
  have h19 := preserves_packed_mul node18 node14 node19 h18 h14 check19
  exact h19

theorem peak_eq : peak = vecMulVec (vector 774) (vector 260) +
    vecMulVec (vector 0) (vector 0) := by
  have h : node19 = plus (outer 774 260) (outer 0 0) := by decide +kernel
  rw [peak, h, matrix_plus, matrix_outer, matrix_outer]

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10
