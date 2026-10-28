module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The degree-65 action for the Suzuki model comparison

These two literal permutations come from a block system of the degree-2080
ATLAS model. The numerical block partition and reproducible discovery are in
`source/blocks.json` and `source/discover.g`; the generator and word conventions
are those of `Tables.lean` and `source/README.md`.

This file defines the actual generated subgroup of Sym(65). It asserts neither
an isomorphism with the fourfold model's quotient nor an identification with
the Suzuki matrix group. Those are separate comparison obligations.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockModel
def aFun (i : Fin 65) : Fin 65 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 6 else 7) else (if i.val < 7 then 4 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 11) else (if i.val < 11 then 8 else 9)) else (if i.val < 14 then (if i.val < 13 then 14 else 16) else (if i.val < 15 then 12 else 19)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 21) else (if i.val < 19 then 22 else 15)) else (if i.val < 22 then (if i.val < 21 then 25 else 17) else (if i.val < 23 then 18 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 28 else 20) else (if i.val < 27 then 26 else 23)) else (if i.val < 30 then (if i.val < 29 then 24 else 33) else (if i.val < 31 then 34 else 36))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 29) else (if i.val < 35 then 30 else 42)) else (if i.val < 38 then (if i.val < 37 then 31 else 44) else (if i.val < 39 then 32 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 49) else (if i.val < 43 then 35 else 51)) else (if i.val < 46 then (if i.val < 45 then 37 else 52) else (if i.val < 47 then 39 else 40)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 56 else 41) else (if i.val < 51 then 53 else 43)) else (if i.val < 54 then (if i.val < 53 then 45 else 50) else (if i.val < 55 then 59 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 48 else 62) else (if i.val < 59 then 63 else 54)) else (if i.val < 62 then (if i.val < 61 then 55 else 64) else (if i.val < 63 then 57 else (if i.val < 64 then 58 else 61)))))))

def bFun (i : Fin 65) : Fin 65 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 18 else 16) else (if i.val < 3 then 21 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 0) else (if i.val < 7 then 49 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 39) else (if i.val < 11 then 34 else 45)) else (if i.val < 14 then (if i.val < 13 then 42 else 31) else (if i.val < 15 then 62 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 51) else (if i.val < 19 then 58 else 27)) else (if i.val < 22 then (if i.val < 21 then 7 else 1) else (if i.val < 23 then 55 else 41))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 33) else (if i.val < 27 then 10 else 64)) else (if i.val < 30 then (if i.val < 29 then 23 else 22) else (if i.val < 31 then 15 else 40))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 36 else 32) else (if i.val < 35 then 43 else 28)) else (if i.val < 38 then (if i.val < 37 then 25 else 60) else (if i.val < 39 then 38 else 44))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 52 else 35) else (if i.val < 43 then 54 else 26)) else (if i.val < 46 then (if i.val < 45 then 4 else 46) else (if i.val < 47 then 53 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 59 else 8) else (if i.val < 51 then 57 else 61)) else (if i.val < 54 then (if i.val < 53 then 13 else 11) else (if i.val < 55 then 24 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 14) else (if i.val < 59 then 5 else 37)) else (if i.val < 62 then (if i.val < 61 then 48 else 56) else (if i.val < 63 then 50 else (if i.val < 64 then 19 else 63)))))))


def a : Equiv.Perm (Fin 65) where
  toFun := aFun
  invFun := aFun
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def b : Equiv.Perm (Fin 65) where
  toFun := bFun
  invFun := fun i => bFun (bFun (bFun i))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def subgroup : Subgroup (Equiv.Perm (Fin 65)) := Subgroup.closure {a, b}
abbrev Model := subgroup

def generatorA : Model := ⟨a, Subgroup.subset_closure (by simp)⟩
def generatorB : Model := ⟨b, Subgroup.subset_closure (by simp)⟩

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockModel
