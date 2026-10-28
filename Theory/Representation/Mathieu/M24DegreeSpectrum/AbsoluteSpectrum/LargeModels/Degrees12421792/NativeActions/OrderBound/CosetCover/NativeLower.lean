module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.Subgroup
public import Theory.GroupTheory.CosetWordCertificate.Schreier
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# A lower bound for the literal max8 subgroup

Its native permutation image is transitive on 24 points and contains explicit
elements of orders 11 and 23. Lagrange's theorem therefore makes its order
divisible by lcm(24,11,23) = 6072. The marked homomorphism transfers this
lower bound to `boundSubgroup` whenever that abstract subgroup is finite.
No recognition as PSL₂(23), injectivity, or local presentation relation is used.

Source marking: ATLAS M24G1-max8W1, retained in `../source/README.md`.
The short witnesses below are checked on the actual native generators.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.NativeLower
open Subgroup.CosetWordCertificate
open Sporadic.Mathieu

def nativeGenerator : Fin 2 → Equiv.Perm (Fin 24) := subgroupWord m24GeneratorA m24GeneratorB

private def table_a : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 20 else (if i.val < 2 then 4 else 7)) else (if i.val < 4 then 17 else (if i.val < 5 then 1 else 13))) else (if i.val < 9 then (if i.val < 7 then 9 else (if i.val < 8 then 2 else 15)) else (if i.val < 10 then 6 else (if i.val < 11 then 19 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 21 else (if i.val < 14 then 5 else 16)) else (if i.val < 16 then 8 else (if i.val < 17 then 14 else 3))) else (if i.val < 21 then (if i.val < 19 then 11 else (if i.val < 20 then 10 else 0)) else (if i.val < 22 then 12 else (if i.val < 23 then 23 else 22)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 20 else (if i.val < 2 then 4 else 7)) else (if i.val < 4 then 17 else (if i.val < 5 then 1 else 13))) else (if i.val < 9 then (if i.val < 7 then 9 else (if i.val < 8 then 2 else 15)) else (if i.val < 10 then 6 else (if i.val < 11 then 19 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 21 else (if i.val < 14 then 5 else 16)) else (if i.val < 16 then 8 else (if i.val < 17 then 14 else 3))) else (if i.val < 21 then (if i.val < 19 then 11 else (if i.val < 20 then 10 else 0)) else (if i.val < 22 then 12 else (if i.val < 23 then 23 else 22)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_b : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 23 else (if i.val < 2 then 4 else 21)) else (if i.val < 4 then 9 else (if i.val < 5 then 6 else 18))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 7 else 8)) else (if i.val < 10 then 15 else (if i.val < 11 then 5 else 11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 12 else (if i.val < 14 then 17 else 2)) else (if i.val < 16 then 3 else (if i.val < 17 then 13 else 16))) else (if i.val < 21 then (if i.val < 19 then 10 else (if i.val < 20 then 0 else 20)) else (if i.val < 22 then 14 else (if i.val < 23 then 22 else 19)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 19 else (if i.val < 2 then 6 else 14)) else (if i.val < 4 then 15 else (if i.val < 5 then 1 else 10))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 7 else 8)) else (if i.val < 10 then 3 else (if i.val < 11 then 18 else 11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 12 else (if i.val < 14 then 16 else 21)) else (if i.val < 16 then 9 else (if i.val < 17 then 17 else 13))) else (if i.val < 21 then (if i.val < 19 then 5 else (if i.val < 20 then 23 else 20)) else (if i.val < 22 then 2 else (if i.val < 23 then 22 else 0)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_c : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 20 else (if i.val < 2 then 6 else 7)) else (if i.val < 4 then 16 else (if i.val < 5 then 4 else 17))) else (if i.val < 9 then (if i.val < 7 then 15 else (if i.val < 8 then 21 else 3)) else (if i.val < 10 then 1 else (if i.val < 11 then 0 else 10)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 14 else (if i.val < 14 then 18 else 13)) else (if i.val < 16 then 8 else (if i.val < 17 then 2 else 9))) else (if i.val < 21 then (if i.val < 19 then 11 else (if i.val < 20 then 5 else 23)) else (if i.val < 22 then 12 else (if i.val < 23 then 19 else 22)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 10 else (if i.val < 2 then 9 else 16)) else (if i.val < 4 then 8 else (if i.val < 5 then 4 else 19))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 2 else 15)) else (if i.val < 10 then 17 else (if i.val < 11 then 11 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 21 else (if i.val < 14 then 14 else 12)) else (if i.val < 16 then 6 else (if i.val < 17 then 3 else 5))) else (if i.val < 21 then (if i.val < 19 then 13 else (if i.val < 20 then 22 else 0)) else (if i.val < 22 then 7 else (if i.val < 23 then 23 else 20)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_d : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 20 else (if i.val < 2 then 1 else 7)) else (if i.val < 4 then 13 else (if i.val < 5 then 6 else 16))) else (if i.val < 9 then (if i.val < 7 then 3 else (if i.val < 8 then 14 else 9)) else (if i.val < 10 then 4 else (if i.val < 11 then 23 else 5)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 2 else (if i.val < 14 then 10 else 17)) else (if i.val < 16 then 8 else (if i.val < 17 then 21 else 15))) else (if i.val < 21 then (if i.val < 19 then 11 else (if i.val < 20 then 18 else 19)) else (if i.val < 22 then 12 else (if i.val < 23 then 0 else 22)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 22 else (if i.val < 2 then 1 else 12)) else (if i.val < 4 then 6 else (if i.val < 5 then 9 else 11))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 2 else 15)) else (if i.val < 10 then 8 else (if i.val < 11 then 13 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 21 else (if i.val < 14 then 3 else 7)) else (if i.val < 16 then 17 else (if i.val < 17 then 5 else 14))) else (if i.val < 21 then (if i.val < 19 then 19 else (if i.val < 20 then 20 else 0)) else (if i.val < 22 then 16 else (if i.val < 23 then 23 else 10)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_e : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 19 else (if i.val < 2 then 3 else 14)) else (if i.val < 4 then 21 else (if i.val < 5 then 6 else 15))) else (if i.val < 9 then (if i.val < 7 then 8 else (if i.val < 8 then 12 else 13)) else (if i.val < 10 then 1 else (if i.val < 11 then 20 else 23)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 17 else (if i.val < 14 then 11 else 10)) else (if i.val < 16 then 9 else (if i.val < 17 then 7 else 4))) else (if i.val < 21 then (if i.val < 19 then 5 else (if i.val < 20 then 16 else 22)) else (if i.val < 22 then 2 else (if i.val < 23 then 18 else 0)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 23 else (if i.val < 2 then 9 else 21)) else (if i.val < 4 then 1 else (if i.val < 5 then 17 else 18))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 16 else 6)) else (if i.val < 10 then 15 else (if i.val < 11 then 14 else 13)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 7 else (if i.val < 14 then 8 else 2)) else (if i.val < 16 then 5 else (if i.val < 17 then 19 else 12))) else (if i.val < 21 then (if i.val < 19 then 22 else (if i.val < 20 then 0 else 10)) else (if i.val < 22 then 3 else (if i.val < 23 then 20 else 11)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_e11 : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 23 else (if i.val < 2 then 9 else 21)) else (if i.val < 4 then 1 else (if i.val < 5 then 17 else 18))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 16 else 6)) else (if i.val < 10 then 15 else (if i.val < 11 then 14 else 13)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 7 else (if i.val < 14 then 8 else 2)) else (if i.val < 16 then 5 else (if i.val < 17 then 19 else 12))) else (if i.val < 21 then (if i.val < 19 then 22 else (if i.val < 20 then 0 else 10)) else (if i.val < 22 then 3 else (if i.val < 23 then 20 else 11)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 19 else (if i.val < 2 then 3 else 14)) else (if i.val < 4 then 21 else (if i.val < 5 then 6 else 15))) else (if i.val < 9 then (if i.val < 7 then 8 else (if i.val < 8 then 12 else 13)) else (if i.val < 10 then 1 else (if i.val < 11 then 20 else 23)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 17 else (if i.val < 14 then 11 else 10)) else (if i.val < 16 then 9 else (if i.val < 17 then 7 else 4))) else (if i.val < 21 then (if i.val < 19 then 5 else (if i.val < 20 then 16 else 22)) else (if i.val < 22 then 2 else (if i.val < 23 then 18 else 0)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_c7 : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 9 else (if i.val < 2 then 7 else 11)) else (if i.val < 4 then 13 else (if i.val < 5 then 4 else 3))) else (if i.val < 9 then (if i.val < 7 then 21 else (if i.val < 8 then 10 else 14)) else (if i.val < 10 then 2 else (if i.val < 11 then 17 else 5)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 20 else (if i.val < 14 then 22 else 23)) else (if i.val < 16 then 12 else (if i.val < 17 then 18 else 16))) else (if i.val < 21 then (if i.val < 19 then 19 else (if i.val < 20 then 8 else 1)) else (if i.val < 22 then 0 else (if i.val < 23 then 15 else 6)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 21 else (if i.val < 2 then 20 else 9)) else (if i.val < 4 then 5 else (if i.val < 5 then 4 else 11))) else (if i.val < 9 then (if i.val < 7 then 23 else (if i.val < 8 then 1 else 19)) else (if i.val < 10 then 0 else (if i.val < 11 then 7 else 2)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 15 else (if i.val < 14 then 3 else 8)) else (if i.val < 16 then 22 else (if i.val < 17 then 17 else 10))) else (if i.val < 21 then (if i.val < 19 then 16 else (if i.val < 20 then 18 else 12)) else (if i.val < 22 then 6 else (if i.val < 23 then 13 else 14)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_t : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 15 else (if i.val < 2 then 16 else 13)) else (if i.val < 4 then 8 else (if i.val < 5 then 17 else 1))) else (if i.val < 9 then (if i.val < 7 then 3 else (if i.val < 8 then 14 else 2)) else (if i.val < 10 then 21 else (if i.val < 11 then 12 else 18)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 10 else (if i.val < 14 then 20 else 11)) else (if i.val < 16 then 7 else (if i.val < 17 then 22 else 19))) else (if i.val < 21 then (if i.val < 19 then 0 else (if i.val < 20 then 6 else 9)) else (if i.val < 22 then 23 else (if i.val < 23 then 5 else 4)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 18 else (if i.val < 2 then 5 else 8)) else (if i.val < 4 then 6 else (if i.val < 5 then 23 else 22))) else (if i.val < 9 then (if i.val < 7 then 19 else (if i.val < 8 then 15 else 3)) else (if i.val < 10 then 20 else (if i.val < 11 then 12 else 14)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 10 else (if i.val < 14 then 2 else 7)) else (if i.val < 16 then 0 else (if i.val < 17 then 1 else 4))) else (if i.val < 21 then (if i.val < 19 then 11 else (if i.val < 20 then 17 else 13)) else (if i.val < 22 then 9 else (if i.val < 23 then 16 else 21)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_e3 : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 7 else (if i.val < 2 then 2 else 20)) else (if i.val < 4 then 14 else (if i.val < 5 then 13 else 1))) else (if i.val < 9 then (if i.val < 7 then 11 else (if i.val < 8 then 4 else 23)) else (if i.val < 10 then 21 else (if i.val < 11 then 18 else 19)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 6 else (if i.val < 14 then 0 else 22)) else (if i.val < 16 then 3 else (if i.val < 17 then 17 else 8))) else (if i.val < 21 then (if i.val < 19 then 9 else (if i.val < 20 then 12 else 5)) else (if i.val < 22 then 10 else (if i.val < 23 then 15 else 16)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 13 else (if i.val < 2 then 5 else 1)) else (if i.val < 4 then 15 else (if i.val < 5 then 7 else 20))) else (if i.val < 9 then (if i.val < 7 then 12 else (if i.val < 8 then 0 else 17)) else (if i.val < 10 then 18 else (if i.val < 11 then 21 else 6)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 19 else (if i.val < 14 then 4 else 3)) else (if i.val < 16 then 22 else (if i.val < 17 then 23 else 16))) else (if i.val < 21 then (if i.val < 19 then 10 else (if i.val < 20 then 11 else 2)) else (if i.val < 22 then 9 else (if i.val < 23 then 14 else 8)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def table_y : Equiv.Perm (Fin 24) where
  toFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 21 else (if i.val < 2 then 16 else 4)) else (if i.val < 4 then 18 else (if i.val < 5 then 22 else 7))) else (if i.val < 9 then (if i.val < 7 then 10 else (if i.val < 8 then 8 else 11)) else (if i.val < 10 then 1 else (if i.val < 11 then 3 else 5)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 0 else (if i.val < 14 then 9 else 17)) else (if i.val < 16 then 14 else (if i.val < 17 then 13 else 20))) else (if i.val < 21 then (if i.val < 19 then 6 else (if i.val < 20 then 2 else 15)) else (if i.val < 22 then 23 else (if i.val < 23 then 19 else 12)))))
  invFun := fun i => (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 12 else (if i.val < 2 then 9 else 19)) else (if i.val < 4 then 10 else (if i.val < 5 then 2 else 11))) else (if i.val < 9 then (if i.val < 7 then 18 else (if i.val < 8 then 5 else 7)) else (if i.val < 10 then 13 else (if i.val < 11 then 6 else 8)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 23 else (if i.val < 14 then 16 else 15)) else (if i.val < 16 then 20 else (if i.val < 17 then 1 else 14))) else (if i.val < 21 then (if i.val < 19 then 3 else (if i.val < 20 then 22 else 17)) else (if i.val < 22 then 0 else (if i.val < 23 then 4 else 21)))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem table_a_eq : m24GeneratorA = table_a := by decide +kernel

private theorem table_b_eq : m24GeneratorB = table_b := by decide +kernel

private theorem table_c_eq : table_b * table_a = table_c := by decide +kernel

private theorem table_d_eq : table_b * table_c = table_d := by decide +kernel

private theorem table_e_eq : table_d * table_c = table_e := by decide +kernel

private theorem table_e11_eq : table_e ^ 11 = table_e11 := by decide +kernel

private theorem table_c7_eq : table_c ^ 7 = table_c7 := by decide +kernel

private theorem table_t_eq : table_e11 * table_c7 = table_t := by decide +kernel

private theorem table_e3_eq : table_e ^ 3 = table_e3 := by decide +kernel

private theorem table_y_eq : table_t * table_e3 * table_t⁻¹ = table_y := by decide +kernel

private def tableGenerator : Fin 2 → Equiv.Perm (Fin 24) := ![table_a, table_y]

private theorem nativeGenerator_eq_table : nativeGenerator = tableGenerator := by
  funext s
  fin_cases s
  · exact table_a_eq
  · change (m24GeneratorB * (m24GeneratorB * m24GeneratorA) *
        (m24GeneratorB * m24GeneratorA)) ^ 11 * (m24GeneratorB * m24GeneratorA) ^ 7 *
        (m24GeneratorB * (m24GeneratorB * m24GeneratorA) *
          (m24GeneratorB * m24GeneratorA)) ^ 3 *
        ((m24GeneratorB * (m24GeneratorB * m24GeneratorA) *
          (m24GeneratorB * m24GeneratorA)) ^ 11 *
          (m24GeneratorB * m24GeneratorA) ^ 7)⁻¹ = table_y
    rw [table_a_eq, table_b_eq, table_c_eq, table_d_eq, table_e_eq,
      table_e11_eq, table_c7_eq, table_t_eq, table_e3_eq, table_y_eq]

def nativeSubgroup : Subgroup (Equiv.Perm (Fin 24)) := Subgroup.closure (Set.range nativeGenerator)

def element (w : Word (Fin 2)) : nativeSubgroup :=
  ⟨eval nativeGenerator w, eval_mem_of_generators_mem nativeSubgroup nativeGenerator
    (fun s => Subgroup.subset_closure (Set.mem_range_self s)) w⟩

def orbitWord : Fin 24 → Word (Fin 2) :=
  ![[],
    [(1, false), (0, true), (1, true), (1, true), (0, true)],
    [(0, true), (1, false), (0, true), (1, true), (0, true)],
    [(0, true), (1, false), (0, true)],
    [(1, false), (0, true), (1, true), (1, true)],
    [(1, true), (1, true), (0, true), (1, true), (0, true)],
    [(1, true), (1, true), (0, true), (1, false), (0, true)],
    [(1, false), (0, true), (1, true), (0, true)],
    [(0, true), (1, true), (0, true)],
    [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true)],
    [(1, false), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, true), (0, true)],
    [(1, false)],
    [(1, true), (0, true), (1, true), (1, true), (0, true)],
    [(1, true), (1, true), (0, true)],
    [(1, true), (0, true)],
    [(0, true), (1, true), (1, true), (0, true)],
    [(1, false), (0, true)],
    [(1, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, true), (1, true)],
    [(0, true)],
    [(1, true)],
    [(0, true), (1, true), (1, true)],
    [(1, true), (1, true)]]

private theorem orbitWord_apply : ∀ i : Fin 24, eval nativeGenerator (orbitWord i) 0 = i := by
  rw [nativeGenerator_eq_table]
  decide +kernel

theorem native_pretransitive : MulAction.IsPretransitive nativeSubgroup (Fin 24) := by
  rw [MulAction.isPretransitive_iff_base (0 : Fin 24)]
  intro i
  exact ⟨element (orbitWord i), orbitWord_apply i⟩

def elevenWord : Word (Fin 2) := [(0, true), (1, true), (1, true)]
def twentyThreeWord : Word (Fin 2) := [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false)]

private theorem eleven_checks : eval nativeGenerator elevenWord ^ 11 = 1 ∧
    eval nativeGenerator elevenWord ≠ 1 := by
  rw [nativeGenerator_eq_table]
  decide +kernel

private theorem twentyThree_checks : eval nativeGenerator twentyThreeWord ^ 23 = 1 ∧
    eval nativeGenerator twentyThreeWord ≠ 1 := by
  rw [nativeGenerator_eq_table]
  decide +kernel

private theorem prime_dvd_card (p : ℕ) [Fact p.Prime] (w : Word (Fin 2))
    (hc : eval nativeGenerator w ^ p = 1 ∧ eval nativeGenerator w ≠ 1) :
    p ∣ Nat.card nativeSubgroup := by
  have ho : orderOf (eval nativeGenerator w) = p := orderOf_eq_prime hc.1 hc.2
  have h := (orderOf_map_dvd nativeSubgroup.subtype (element w)).trans
    (orderOf_dvd_natCard (element w))
  change orderOf (eval nativeGenerator w) ∣ Nat.card nativeSubgroup at h
  rwa [ho] at h

theorem native_card_dvd : 6072 ∣ Nat.card nativeSubgroup := by
  have := native_pretransitive
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have h24 : 24 ∣ Nat.card nativeSubgroup := by
    have h := (MulAction.stabilizer nativeSubgroup (0 : Fin 24)).index_dvd_card
    simpa only [MulAction.index_stabilizer_of_transitive, Nat.card_fin] using h
  have h11 := prime_dvd_card 11 elevenWord eleven_checks
  have h23 := prime_dvd_card 23 twentyThreeWord twentyThree_checks
  have h := Nat.lcm_dvd h24 (Nat.lcm_dvd h11 h23)
  norm_num at h ⊢
  exact h

noncomputable def nativeMap : UniversalGroup →* Equiv.Perm (Fin 24) := M24.subtype.comp toCarrier

theorem nativeMap_boundGenerator (s : Fin 2) : nativeMap (boundGenerator s) = nativeGenerator s := by
  have ha : nativeMap (generator 0) = m24GeneratorA := by
    change (toCarrier (PresentedGroup.of 0)).val = _
    rw [toCarrier_zero]
    rfl
  have hb : nativeMap (generator 1) = m24GeneratorB := by
    change (toCarrier (PresentedGroup.of 1)).val = _
    rw [toCarrier_one]
    rfl
  rw [boundGenerator, map_subgroupWord, ha, hb]
  rfl

theorem map_boundSubgroup : boundSubgroup.map nativeMap = nativeSubgroup := by
  rw [boundSubgroup, MonoidHom.map_closure, ← Set.range_comp]
  have he : nativeMap ∘ boundGenerator = nativeGenerator := funext nativeMap_boundGenerator
  rw [he]
  rfl

/-- The literal source subgroup has at least 6072 elements whenever it is finite. -/
theorem boundSubgroup_card_ge [Finite boundSubgroup] : 6072 ≤ Nat.card boundSubgroup := by
  have h := boundSubgroup.card_map_dvd nativeMap
  rw [map_boundSubgroup] at h
  exact Nat.le_of_dvd Nat.card_pos (native_card_dvd.trans h)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.NativeLower
