module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation
public import Mathlib.LinearAlgebra.Matrix.Notation
/-!
# Transporters fixing the original native trio

Three explicit permutations preserve the published Golay generating rows and
the standard trio. They will supply edges of a descending transporter forest
on the existing trio catalogue; no generation assertion is assumed.

Source: Aschbacher–Segev (1991), (3.4), applied in (5.4)(1), pp.594,600.
The retained GAP discovery data are checked independently by the Lean kernel.
-/
@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
def permTable : Fin 3 → Fin 24 → Fin 24 :=
  ![![10, 2, 1, 16, 15, 19, 8, 18, 6, 11, 0, 9, 21, 14, 13, 4, 3, 20, 7, 5, 17, 12, 23, 22],
    ![20, 14, 7, 9, 13, 17, 16, 2, 18, 3, 12, 21, 10, 4, 1, 23, 6, 5, 8, 22, 0, 11, 19, 15],
    ![10, 23, 2, 0, 8, 18, 14, 12, 17, 9, 3, 11, 19, 13, 20, 15, 16, 4, 21, 7, 6, 5, 1, 22]]

def inverseTable : Fin 3 → Fin 24 → Fin 24 :=
  ![![10, 2, 1, 16, 15, 19, 8, 18, 6, 11, 0, 9, 21, 14, 13, 4, 3, 20, 7, 5, 17, 12, 23, 22],
    ![20, 14, 7, 9, 13, 17, 16, 2, 18, 3, 12, 21, 10, 4, 1, 23, 6, 5, 8, 22, 0, 11, 19, 15],
    ![3, 22, 2, 10, 17, 21, 20, 19, 4, 9, 0, 11, 7, 13, 6, 15, 16, 8, 5, 12, 14, 18, 23, 1]]

def generatorPerm (k : Fin 3) : Equiv.Perm (Fin 24) where
  toFun := permTable k
  invFun := inverseTable k
  left_inv := by revert k; decide +kernel
  right_inv := by revert k; decide +kernel

def rowMessage : Fin 3 → Fin 12 → Fin 4096 :=
  ![![2064, 53, 2179, 169, 2105, 2216, 416, 25, 2289, 3209, 664, 2104],
    ![1059, 1056, 418, 865, 2146, 1378, 1281, 69, 259, 1355, 1376, 1107],
    ![112, 186, 30, 219, 408, 176, 226, 74, 200, 616, 1074, 2274]]

theorem row_images (k : Fin 3) (i : Fin 12) :
    m24PermuteMask (generatorPerm k) (m24GolayRow i) =
      m24GolayCode (rowMessage k i) := by
  revert k i
  decide +kernel

theorem generator_mem (k : Fin 3) : generatorPerm k ∈ M24 :=
  PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows _
    (fun i => ⟨rowMessage k i,row_images k i⟩)

theorem generator_fixes_trio (k : Fin 3) :
    generatorPerm k • standardTrio.parts = standardTrio.parts := by
  revert k
  decide +kernel

noncomputable def nativeGenerator (k : Fin 3) : trioStabilizer standardTrio :=
  ⟨⟨generatorPerm k,generator_mem k⟩,generator_fixes_trio k⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
