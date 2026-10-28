module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.MatrixValues
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks00
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks01
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks02
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks03
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks04
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks05
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks06
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks07
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks08
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks09
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Relations.Checks10
import Mathlib.Tactic.FinCases

/-!
# The six Suzuki relations for the concrete HN local generators

The fixed words in `Words.lean` satisfy Suzuki's presentation (2.15), in the
indexing of `LocalSuzukiCertificate`. The numerical matrix identities are
certified by packed row arithmetic in `Relations/Checks*.lean`; injectivity
of `matrixHom` transfers them to the original subgroup elements.

This proves only the relations. Generation is a separate obligation, and no
order or identification of the local subgroup is used. Matrix provenance:
`../../MatrixSources.md`; word provenance: `source/README.md`.
-/

public section
namespace HaradaNorton.OrderCertificate

open LocalRelationChecks

private theorem matrix_tail_square (i : Fin 10) (hi : i ≠ 0) :
    localSuzukiMatrix i ^ 2 = 1 := by
  fin_cases i
  · exact (hi rfl).elim
  · exact tail_square1
  · exact tail_square2
  · exact tail_square3
  · exact tail_square4
  · exact tail_square5
  · exact tail_square6
  · exact tail_square7
  · exact tail_square8
  · exact tail_square9

private theorem matrix_tail_adjacent_cube (i : Fin 9) (hi : i ≠ 0) :
    (localSuzukiMatrix i.castSucc * localSuzukiMatrix i.succ) ^ 3 = 1 := by
  fin_cases i
  · exact (hi rfl).elim
  · exact adjacent_cube1
  · exact adjacent_cube2
  · exact adjacent_cube3
  · exact adjacent_cube4
  · exact adjacent_cube5
  · exact adjacent_cube6
  · exact adjacent_cube7
  · exact adjacent_cube8

private theorem matrix_root_far_square (j : Fin 10) (hj : 1 < j.val) :
    (localSuzukiMatrix 0 * localSuzukiMatrix j) ^ 2 = 1 := by
  fin_cases j
  · exact (Nat.not_lt_zero 1 hj).elim
  · exact (Nat.lt_irrefl 1 hj).elim
  · exact root_far_square2
  · exact root_far_square3
  · exact root_far_square4
  · exact root_far_square5
  · exact root_far_square6
  · exact root_far_square7
  · exact root_far_square8
  · exact root_far_square9

private theorem matrix_tail_far_commute (i j : Fin 10) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (localSuzukiMatrix i) (localSuzukiMatrix j) := by
  fin_cases i <;> fin_cases j
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hi rfl).elim
  · exact (hj rfl).elim
  · exact ((by decide : ¬ (1 + 1 < 1 ∨ 1 + 1 < 1)) hij).elim
  · exact ((by decide : ¬ (1 + 1 < 2 ∨ 2 + 1 < 1)) hij).elim
  · exact tail_commute1_3
  · exact tail_commute1_4
  · exact tail_commute1_5
  · exact tail_commute1_6
  · exact tail_commute1_7
  · exact tail_commute1_8
  · exact tail_commute1_9
  · exact (hj rfl).elim
  · exact ((by decide : ¬ (2 + 1 < 1 ∨ 1 + 1 < 2)) hij).elim
  · exact ((by decide : ¬ (2 + 1 < 2 ∨ 2 + 1 < 2)) hij).elim
  · exact ((by decide : ¬ (2 + 1 < 3 ∨ 3 + 1 < 2)) hij).elim
  · exact tail_commute2_4
  · exact tail_commute2_5
  · exact tail_commute2_6
  · exact tail_commute2_7
  · exact tail_commute2_8
  · exact tail_commute2_9
  · exact (hj rfl).elim
  · exact tail_commute1_3.symm
  · exact ((by decide : ¬ (3 + 1 < 2 ∨ 2 + 1 < 3)) hij).elim
  · exact ((by decide : ¬ (3 + 1 < 3 ∨ 3 + 1 < 3)) hij).elim
  · exact ((by decide : ¬ (3 + 1 < 4 ∨ 4 + 1 < 3)) hij).elim
  · exact tail_commute3_5
  · exact tail_commute3_6
  · exact tail_commute3_7
  · exact tail_commute3_8
  · exact tail_commute3_9
  · exact (hj rfl).elim
  · exact tail_commute1_4.symm
  · exact tail_commute2_4.symm
  · exact ((by decide : ¬ (4 + 1 < 3 ∨ 3 + 1 < 4)) hij).elim
  · exact ((by decide : ¬ (4 + 1 < 4 ∨ 4 + 1 < 4)) hij).elim
  · exact ((by decide : ¬ (4 + 1 < 5 ∨ 5 + 1 < 4)) hij).elim
  · exact tail_commute4_6
  · exact tail_commute4_7
  · exact tail_commute4_8
  · exact tail_commute4_9
  · exact (hj rfl).elim
  · exact tail_commute1_5.symm
  · exact tail_commute2_5.symm
  · exact tail_commute3_5.symm
  · exact ((by decide : ¬ (5 + 1 < 4 ∨ 4 + 1 < 5)) hij).elim
  · exact ((by decide : ¬ (5 + 1 < 5 ∨ 5 + 1 < 5)) hij).elim
  · exact ((by decide : ¬ (5 + 1 < 6 ∨ 6 + 1 < 5)) hij).elim
  · exact tail_commute5_7
  · exact tail_commute5_8
  · exact tail_commute5_9
  · exact (hj rfl).elim
  · exact tail_commute1_6.symm
  · exact tail_commute2_6.symm
  · exact tail_commute3_6.symm
  · exact tail_commute4_6.symm
  · exact ((by decide : ¬ (6 + 1 < 5 ∨ 5 + 1 < 6)) hij).elim
  · exact ((by decide : ¬ (6 + 1 < 6 ∨ 6 + 1 < 6)) hij).elim
  · exact ((by decide : ¬ (6 + 1 < 7 ∨ 7 + 1 < 6)) hij).elim
  · exact tail_commute6_8
  · exact tail_commute6_9
  · exact (hj rfl).elim
  · exact tail_commute1_7.symm
  · exact tail_commute2_7.symm
  · exact tail_commute3_7.symm
  · exact tail_commute4_7.symm
  · exact tail_commute5_7.symm
  · exact ((by decide : ¬ (7 + 1 < 6 ∨ 6 + 1 < 7)) hij).elim
  · exact ((by decide : ¬ (7 + 1 < 7 ∨ 7 + 1 < 7)) hij).elim
  · exact ((by decide : ¬ (7 + 1 < 8 ∨ 8 + 1 < 7)) hij).elim
  · exact tail_commute7_9
  · exact (hj rfl).elim
  · exact tail_commute1_8.symm
  · exact tail_commute2_8.symm
  · exact tail_commute3_8.symm
  · exact tail_commute4_8.symm
  · exact tail_commute5_8.symm
  · exact tail_commute6_8.symm
  · exact ((by decide : ¬ (8 + 1 < 7 ∨ 7 + 1 < 8)) hij).elim
  · exact ((by decide : ¬ (8 + 1 < 8 ∨ 8 + 1 < 8)) hij).elim
  · exact ((by decide : ¬ (8 + 1 < 9 ∨ 9 + 1 < 8)) hij).elim
  · exact (hj rfl).elim
  · exact tail_commute1_9.symm
  · exact tail_commute2_9.symm
  · exact tail_commute3_9.symm
  · exact tail_commute4_9.symm
  · exact tail_commute5_9.symm
  · exact tail_commute6_9.symm
  · exact tail_commute7_9.symm
  · exact ((by decide : ¬ (9 + 1 < 8 ∨ 8 + 1 < 9)) hij).elim
  · exact ((by decide : ¬ (9 + 1 < 9 ∨ 9 + 1 < 9)) hij).elim

/-- The distinguished Suzuki generator has cube one. -/
theorem localSuzukiGen_root_cube : localSuzukiGen 0 ^ 3 = 1 := by
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom ((localSuzukiGen 0 : HN) ^ 3) = matrixHom 1
  simpa only [map_pow, map_one, matrixHom_localSuzukiGen] using root_cube

/-- Every other Suzuki generator has square one. -/
theorem localSuzukiGen_tail_square (i : Fin 10) (hi : i ≠ 0) :
    localSuzukiGen i ^ 2 = 1 := by
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom ((localSuzukiGen i : HN) ^ 2) = matrixHom 1
  simpa only [map_pow, map_one, matrixHom_localSuzukiGen] using matrix_tail_square i hi

/-- The product of the root and its adjacent generator has cube one. -/
theorem localSuzukiGen_root_adjacent_cube :
    (localSuzukiGen 0 * localSuzukiGen 1) ^ 3 = 1 := by
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom (((localSuzukiGen 0 : HN) * (localSuzukiGen 1 : HN)) ^ 3) = matrixHom 1
  simpa only [map_pow, map_mul, map_one, matrixHom_localSuzukiGen] using adjacent_cube0

/-- Adjacent generators in the tail have product of cube one. -/
theorem localSuzukiGen_tail_adjacent_cube (i : Fin 9) (hi : i ≠ 0) :
    (localSuzukiGen i.castSucc * localSuzukiGen i.succ) ^ 3 = 1 := by
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom (((localSuzukiGen i.castSucc : HN) *
    (localSuzukiGen i.succ : HN)) ^ 3) = matrixHom 1
  simpa only [map_pow, map_mul, map_one, matrixHom_localSuzukiGen] using
    matrix_tail_adjacent_cube i hi

/-- The root times any nonadjacent generator has square one. -/
theorem localSuzukiGen_root_far_square (j : Fin 10) (hj : 1 < j.val) :
    (localSuzukiGen 0 * localSuzukiGen j) ^ 2 = 1 := by
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom (((localSuzukiGen 0 : HN) * (localSuzukiGen j : HN)) ^ 2) = matrixHom 1
  simpa only [map_pow, map_mul, map_one, matrixHom_localSuzukiGen] using
    matrix_root_far_square j hj

/-- Nonadjacent generators of the tail commute. -/
theorem localSuzukiGen_tail_far_commute (i j : Fin 10) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (localSuzukiGen i) (localSuzukiGen j) := by
  change localSuzukiGen i * localSuzukiGen j = localSuzukiGen j * localSuzukiGen i
  apply Subtype.ext
  apply matrixHom_injective
  change matrixHom ((localSuzukiGen i : HN) * (localSuzukiGen j : HN)) =
    matrixHom ((localSuzukiGen j : HN) * (localSuzukiGen i : HN))
  simpa only [map_mul, matrixHom_localSuzukiGen] using (matrix_tail_far_commute i j hi hj hij).eq

end HaradaNorton.OrderCertificate
