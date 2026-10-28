module
public import Theory.Mathieu.M24.LocalGeometry.Seed
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Certified native generators for the far-trio orbit

These four point permutations preserve the twelve published Golay rows and
stabilize the literal standard sextet. They are used only as transporters;
no assertion that they generate the full stabilizer is needed.

Source: AS91 (3.8), p.595. Tables were discovered by GAP and independently
checked against the native Golay encoder; every assertion below is checked
by the Lean kernel.
-/
@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
def permTable : Fin 4 → Fin 24 → Fin 24 :=
  ![![2, 3, 0, 1, 16, 23, 15, 14, 18, 12, 17, 22, 9, 21, 7, 6, 4, 10, 8, 20, 19, 13, 11, 5],
    ![0, 1, 2, 3, 17, 4, 19, 8, 16, 6, 20, 11, 13, 23, 14, 21, 7, 5, 10, 9, 18, 22, 15, 12],
    ![14, 6, 19, 9, 2, 0, 15, 18, 17, 12, 16, 1, 21, 5, 7, 13, 10, 3, 11, 20, 8, 4, 23, 22],
    ![14, 9, 19, 6, 18, 8, 3, 23, 5, 1, 15, 13, 22, 11, 0, 10, 20, 21, 4, 2, 16, 17, 12, 7]]

def inverseTable : Fin 4 → Fin 24 → Fin 24 :=
  ![![2, 3, 0, 1, 16, 23, 15, 14, 18, 12, 17, 22, 9, 21, 7, 6, 4, 10, 8, 20, 19, 13, 11, 5],
    ![0, 1, 2, 3, 5, 17, 9, 16, 7, 19, 18, 11, 23, 12, 14, 22, 8, 4, 20, 6, 10, 15, 21, 13],
    ![5, 11, 4, 17, 21, 13, 1, 14, 20, 3, 16, 18, 9, 15, 0, 6, 10, 8, 7, 2, 19, 12, 23, 22],
    ![14, 9, 19, 6, 18, 8, 3, 23, 5, 1, 15, 13, 22, 11, 0, 10, 20, 21, 4, 2, 16, 17, 12, 7]]

def generatorPerm (k : Fin 4) : Equiv.Perm (Fin 24) where
  toFun := permTable k
  invFun := inverseTable k
  left_inv := by revert k; decide +kernel
  right_inv := by revert k; decide +kernel

def rowMessage : Fin 4 → Fin 12 → Fin 4096 :=
  ![![2788, 3176, 1953, 1298, 720, 2480, 3872, 1648, 480, 2960, 3920, 3280],
    ![2081, 546, 2084, 680, 2720, 688, 2560, 2432, 512, 2240, 3232, 640],
    ![2456, 2136, 1160, 1800, 2188, 1177, 1296, 2304, 3456, 1424, 3098, 2480],
    ![129, 644, 145, 84, 5, 405, 156, 128, 181, 19, 2064, 1029]]

theorem row_images (k : Fin 4) (i : Fin 12) :
    m24PermuteMask (generatorPerm k) (m24GolayRow i) =
      m24GolayCode (rowMessage k i) := by
  revert k i
  decide +kernel

theorem generator_mem (k : Fin 4) : generatorPerm k ∈ M24 :=
  PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows _
    (fun i => ⟨rowMessage k i, row_images k i⟩)

theorem generator_fixes_sextet (k : Fin 4) :
    generatorPerm k • standardSextet.parts = standardSextet.parts := by
  revert k
  decide +kernel

noncomputable def nativeGenerator (k : Fin 4) : sextetStabilizer standardSextet :=
  ⟨⟨generatorPerm k, generator_mem k⟩, generator_fixes_sextet k⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
