module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Field

/-!
# The explicit matrix pair and native triple over F₈

The two displayed matrices are the witnesses from `source/matrices.json`.
The three further matrices are root(1,0), diag(v³,v²,v⁻²,v⁻³), and the
anti-diagonal Weyl matrix. Explicit inverse matrices make arithmetic checks
computable. The generated subgroup is an actual subgroup of GL₄(F₈).

Source: the concrete comparison for Aschbacher–Smith I.1.1 and I.1.3(5),
printed p.407. Data attribution and conventions are in `source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison

def matrixA : GL8 where
  val := !![code 5, code 0, code 1, code 3;
     code 6, code 6, code 2, code 1;
     code 1, code 3, code 6, code 0;
     code 7, code 1, code 6, code 5]
  inv := !![code 5, code 0, code 1, code 3;
     code 6, code 6, code 2, code 1;
     code 1, code 3, code 6, code 0;
     code 7, code 1, code 6, code 5]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def matrixB : GL8 where
  val := !![code 3, code 1, code 6, code 3;
     code 7, code 4, code 4, code 2;
     code 3, code 4, code 3, code 0;
     code 5, code 5, code 6, code 4]
  inv := !![code 4, code 0, code 2, code 3;
     code 6, code 3, code 4, code 6;
     code 5, code 4, code 4, code 1;
     code 5, code 3, code 7, code 3]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def rootOne : GL8 where
  val := !![code 1, code 1, code 0, code 1;
     code 0, code 1, code 1, code 1;
     code 0, code 0, code 1, code 1;
     code 0, code 0, code 0, code 1]
  inv := !![code 1, code 1, code 1, code 1;
     code 0, code 1, code 1, code 0;
     code 0, code 0, code 1, code 1;
     code 0, code 0, code 0, code 1]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def torusV : GL8 where
  val := !![code 4, code 0, code 0, code 0;
     code 0, code 3, code 0, code 0;
     code 0, code 0, code 6, code 0;
     code 0, code 0, code 0, code 5]
  inv := !![code 5, code 0, code 0, code 0;
     code 0, code 6, code 0, code 0;
     code 0, code 0, code 3, code 0;
     code 0, code 0, code 0, code 4]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def weyl : GL8 where
  val := !![code 0, code 0, code 0, code 1;
     code 0, code 0, code 1, code 0;
     code 0, code 1, code 0, code 0;
     code 1, code 0, code 0, code 0]
  inv := !![code 0, code 0, code 0, code 1;
     code 0, code 0, code 1, code 0;
     code 0, code 1, code 0, code 0;
     code 1, code 0, code 0, code 0]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def pairSubgroup : Subgroup GL8 := Subgroup.closure {matrixA, matrixB}
abbrev PairModel := pairSubgroup

def pairA : PairModel := ⟨matrixA, Subgroup.subset_closure (by simp)⟩
def pairB : PairModel := ⟨matrixB, Subgroup.subset_closure (by simp)⟩

def tripleSubgroup : Subgroup GL8 := Subgroup.closure {rootOne, torusV, weyl}

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison
