module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.IntegralKernel.Arithmetic
/-!
# Kernel-checked integral row certificate

For each of the 768 table entries (756 distinct rows), the three destination
indices certify its product by A, B, and B⁻¹. Each 32-row block is checked
separately. The fibre checks compare only the six standard basis reductions.
Sparse row formulas are proved in `Arithmetic`. All certificate arithmetic
is evaluated by Lean's kernel; the search script is not trusted.

Numerical source: John Bray, ATLAS `6L34G1-Ar6aB0.M`; see `MatrixData`.
-/
public section
open Atlas.Algebra Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.IntegralKernel
attribute [local irreducible] rows

private def destA0 : Fin 32 → Fin 24 × Fin 32 :=
  ![(23, 19), (23, 18), (21, 3), (21, 2), (21, 8), (21, 7), (21, 13), (21, 5), (21, 4), (21, 10), (21, 9), (21, 15), (21, 14), (21, 6), (21, 12), (21, 11), (21, 31), (21, 30), (22, 1), (22, 0), (22, 11), (22, 10), (22, 13), (22, 12), (22, 22), (22, 26), (22, 25), (22, 24), (22, 23), (22, 27), (21, 17), (21, 16)]

attribute [local irreducible] destA0

set_option Elab.async false in
private theorem checkA0 : ∀ i : Fin 32,
    stepA (rows 0 i) = rows (destA0 i).1 (destA0 i).2 := by
  decide +kernel

private def destA1 : Fin 32 → Fin 24 × Fin 32 :=
  ![(21, 19), (21, 18), (22, 3), (22, 2), (22, 5), (22, 4), (22, 29), (22, 28), (22, 31), (22, 30), (21, 21), (21, 20), (21, 23), (21, 22), (22, 15), (22, 14), (22, 17), (22, 16), (23, 1), (23, 0), (23, 3), (23, 2), (21, 24), (21, 28), (21, 27), (21, 26), (21, 25), (21, 29), (22, 7), (22, 6), (22, 9), (22, 8)]

attribute [local irreducible] destA1

set_option Elab.async false in
private theorem checkA1 : ∀ i : Fin 32,
    stepA (rows 1 i) = rows (destA1 i).1 (destA1 i).2 := by
  decide +kernel

private def destA2 : Fin 32 → Fin 24 × Fin 32 :=
  ![(22, 19), (22, 18), (22, 21), (22, 20), (23, 8), (23, 7), (23, 13), (23, 5), (23, 4), (23, 10), (23, 9), (23, 15), (23, 14), (23, 6), (23, 12), (23, 11), (23, 17), (23, 16), (18, 31), (18, 20), (18, 19), (18, 22), (18, 21), (19, 1), (19, 0), (19, 3), (19, 2), (19, 27), (19, 26), (19, 29), (19, 28), (18, 18)]

attribute [local irreducible] destA2

set_option Elab.async false in
private theorem checkA2 : ∀ i : Fin 32,
    stepA (rows 2 i) = rows (destA2 i).1 (destA2 i).2 := by
  decide +kernel

private def destA3 : Fin 32 → Fin 24 × Fin 32 :=
  ![(18, 24), (18, 23), (18, 26), (18, 25), (19, 7), (19, 11), (19, 10), (19, 4), (19, 13), (19, 12), (19, 6), (19, 5), (19, 9), (19, 8), (19, 15), (19, 14), (19, 30), (20, 2), (20, 1), (20, 0), (19, 31), (20, 3), (20, 22), (20, 21), (20, 24), (20, 23), (18, 28), (18, 27), (18, 30), (18, 29), (19, 16), (19, 20)]

attribute [local irreducible] destA3

set_option Elab.async false in
private theorem checkA3 : ∀ i : Fin 32,
    stepA (rows 3 i) = rows (destA3 i).1 (destA3 i).2 := by
  decide +kernel

private def destA4 : Fin 32 → Fin 24 × Fin 32 :=
  ![(19, 19), (19, 18), (19, 17), (19, 21), (20, 5), (20, 4), (20, 11), (20, 10), (20, 14), (20, 13), (20, 7), (20, 6), (20, 15), (20, 9), (20, 8), (20, 12), (20, 26), (20, 25), (20, 28), (20, 27), (21, 1), (19, 23), (19, 22), (19, 25), (19, 24), (20, 17), (20, 16), (20, 19), (20, 18), (20, 30), (20, 29), (21, 0)]

attribute [local irreducible] destA4

set_option Elab.async false in
private theorem checkA4 : ∀ i : Fin 32,
    stepA (rows 4 i) = rows (destA4 i).1 (destA4 i).2 := by
  decide +kernel

private def destA5 : Fin 32 → Fin 24 × Fin 32 :=
  ![(20, 31), (20, 20), (18, 17), (16, 2), (16, 1), (16, 4), (16, 3), (16, 15), (16, 14), (16, 17), (16, 16), (17, 10), (17, 9), (17, 12), (17, 11), (16, 18), (16, 6), (16, 5), (16, 8), (16, 7), (16, 13), (16, 20), (16, 19), (16, 26), (16, 25), (16, 29), (16, 28), (16, 22), (16, 21), (16, 30), (16, 24), (16, 23)]

attribute [local irreducible] destA5

set_option Elab.async false in
private theorem checkA5 : ∀ i : Fin 32,
    stepA (rows 5 i) = rows (destA5 i).1 (destA5 i).2 := by
  decide +kernel

private def destA6 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 27), (17, 13), (17, 17), (17, 16), (17, 15), (17, 14), (17, 18), (18, 6), (18, 5), (18, 8), (18, 7), (16, 10), (16, 9), (16, 12), (16, 11), (16, 31), (17, 3), (17, 2), (17, 1), (17, 0), (17, 4), (17, 22), (17, 26), (17, 25), (17, 19), (17, 28), (17, 27), (17, 21), (17, 20), (17, 24), (17, 23), (17, 30)]

attribute [local irreducible] destA6

set_option Elab.async false in
private theorem checkA6 : ∀ i : Fin 32,
    stepA (rows 6 i) = rows (destA6 i).1 (destA6 i).2 := by
  decide +kernel

private def destA7 : Fin 32 → Fin 24 × Fin 32 :=
  ![(17, 29), (18, 4), (18, 10), (18, 9), (18, 12), (18, 11), (17, 31), (17, 6), (17, 5), (17, 8), (17, 7), (18, 1), (18, 0), (18, 3), (18, 2), (18, 14), (18, 13), (18, 16), (18, 15), (7, 19), (7, 23), (7, 22), (7, 21), (7, 20), (7, 24), (8, 15), (8, 14), (8, 17), (8, 16), (9, 10), (9, 9), (9, 12)]

attribute [local irreducible] destA7

set_option Elab.async false in
private theorem checkA7 : ∀ i : Fin 32,
    stepA (rows 7 i) = rows (destA7 i).1 (destA7 i).2 := by
  decide +kernel

private def destA8 : Fin 32 → Fin 24 × Fin 32 :=
  ![(9, 11), (10, 8), (10, 7), (10, 13), (10, 5), (10, 4), (10, 10), (10, 9), (10, 15), (10, 14), (10, 6), (10, 12), (10, 11), (15, 6), (7, 26), (7, 25), (7, 28), (7, 27), (8, 18), (8, 22), (8, 21), (8, 20), (8, 19), (8, 23), (10, 17), (10, 16), (10, 23), (10, 22), (10, 26), (10, 25), (10, 19), (10, 18)]

attribute [local irreducible] destA8

set_option Elab.async false in
private theorem checkA8 : ∀ i : Fin 32,
    stepA (rows 8 i) = rows (destA8 i).1 (destA8 i).2 := by
  decide +kernel

private def destA9 : Fin 32 → Fin 24 × Fin 32 :=
  ![(10, 27), (10, 21), (10, 20), (10, 24), (13, 17), (13, 16), (13, 19), (13, 18), (14, 11), (7, 30), (7, 29), (8, 0), (7, 31), (9, 13), (9, 17), (9, 16), (9, 15), (9, 14), (9, 18), (10, 31), (11, 3), (11, 2), (10, 28), (11, 5), (11, 4), (10, 30), (10, 29), (11, 1), (11, 0), (11, 7), (11, 6), (13, 20)]

attribute [local irreducible] destA9

set_option Elab.async false in
private theorem checkA9 : ∀ i : Fin 32,
    stepA (rows 9 i) = rows (destA9 i).1 (destA9 i).2 := by
  decide +kernel

private def destA10 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 13), (14, 12), (14, 15), (14, 14), (8, 5), (8, 4), (8, 10), (8, 2), (8, 1), (8, 7), (8, 6), (8, 12), (8, 11), (8, 3), (8, 9), (8, 8), (8, 25), (8, 24), (8, 31), (8, 30), (9, 2), (9, 1), (8, 27), (8, 26), (9, 3), (8, 29), (8, 28), (9, 0), (9, 22), (9, 26), (9, 25), (9, 19)]

attribute [local irreducible] destA10

set_option Elab.async false in
private theorem checkA10 : ∀ i : Fin 32,
    stepA (rows 10 i) = rows (destA10 i).1 (destA10 i).2 := by
  decide +kernel

private def destA11 : Fin 32 → Fin 24 × Fin 32 :=
  ![(9, 28), (9, 27), (9, 21), (9, 20), (9, 24), (9, 23), (9, 30), (9, 29), (11, 18), (11, 17), (12, 9), (11, 20), (11, 19), (12, 6), (11, 22), (11, 21), (12, 3), (11, 9), (11, 8), (11, 12), (11, 11), (11, 15), (11, 14), (11, 28), (11, 27), (11, 26), (11, 25), (11, 24), (11, 23), (12, 5), (12, 4), (12, 8)]

attribute [local irreducible] destA11

set_option Elab.async false in
private theorem checkA11 : ∀ i : Fin 32,
    stepA (rows 11 i) = rows (destA11 i).1 (destA11 i).2 := by
  decide +kernel

private def destA12 : Fin 32 → Fin 24 × Fin 32 :=
  ![(12, 7), (12, 11), (12, 10), (11, 16), (11, 30), (11, 29), (11, 13), (12, 0), (11, 31), (11, 10), (12, 2), (12, 1), (13, 22), (13, 21), (13, 28), (13, 27), (13, 31), (13, 30), (13, 24), (13, 23), (14, 0), (13, 26), (13, 25), (13, 29), (14, 19), (14, 23), (14, 22), (14, 16), (14, 25), (14, 24), (14, 18), (14, 17)]

attribute [local irreducible] destA12

set_option Elab.async false in
private theorem checkA12 : ∀ i : Fin 32,
    stepA (rows 12 i) = rows (destA12 i).1 (destA12 i).2 := by
  decide +kernel

private def destA13 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 21), (14, 20), (14, 27), (14, 26), (15, 11), (15, 10), (15, 16), (15, 8), (15, 7), (15, 13), (15, 12), (15, 18), (15, 17), (15, 9), (15, 15), (15, 14), (9, 5), (9, 4), (9, 7), (9, 6), (9, 31), (12, 13), (12, 12), (12, 19), (12, 18), (12, 22), (12, 21), (12, 15), (12, 14), (12, 23), (12, 17), (12, 16)]

attribute [local irreducible] destA13

set_option Elab.async false in
private theorem checkA13 : ∀ i : Fin 32,
    stepA (rows 13 i) = rows (destA13 i).1 (destA13 i).2 := by
  decide +kernel

private def destA14 : Fin 32 → Fin 24 × Fin 32 :=
  ![(12, 20), (14, 1), (14, 5), (14, 4), (14, 3), (14, 2), (14, 6), (15, 20), (15, 19), (15, 22), (15, 21), (9, 8), (10, 1), (10, 0), (10, 3), (10, 2), (12, 27), (12, 31), (12, 30), (12, 24), (13, 1), (13, 0), (12, 26), (12, 25), (12, 29), (12, 28), (13, 3), (13, 2), (14, 28), (15, 0), (14, 31), (14, 30)]

attribute [local irreducible] destA14

set_option Elab.async false in
private theorem checkA14 : ∀ i : Fin 32,
    stepA (rows 14 i) = rows (destA14 i).1 (destA14 i).2 := by
  decide +kernel

private def destA15 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 29), (15, 1), (15, 24), (15, 23), (15, 26), (15, 25), (8, 13), (13, 8), (13, 7), (13, 13), (13, 5), (13, 4), (13, 10), (13, 9), (13, 15), (13, 14), (13, 6), (13, 12), (13, 11), (14, 8), (14, 7), (14, 10), (14, 9), (15, 3), (15, 2), (15, 5), (15, 4), (15, 27), (15, 31), (15, 30), (15, 29), (15, 28)]

attribute [local irreducible] destA15

set_option Elab.async false in
private theorem checkA15 : ∀ i : Fin 32,
    stepA (rows 15 i) = rows (destA15 i).1 (destA15 i).2 := by
  decide +kernel

private def destA16 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 0), (5, 4), (5, 3), (5, 6), (5, 5), (5, 17), (5, 16), (5, 19), (5, 18), (6, 12), (6, 11), (6, 14), (6, 13), (5, 20), (5, 8), (5, 7), (5, 10), (5, 9), (5, 15), (5, 22), (5, 21), (5, 28), (5, 27), (5, 31), (5, 30), (5, 24), (5, 23), (6, 0), (5, 26), (5, 25), (5, 29), (6, 15)]

attribute [local irreducible] destA16

set_option Elab.async false in
private theorem checkA16 : ∀ i : Fin 32,
    stepA (rows 16 i) = rows (destA16 i).1 (destA16 i).2 := by
  decide +kernel

private def destA17 : Fin 32 → Fin 24 × Fin 32 :=
  ![(6, 19), (6, 18), (6, 17), (6, 16), (6, 20), (7, 8), (7, 7), (7, 10), (7, 9), (5, 12), (5, 11), (5, 14), (5, 13), (6, 1), (6, 5), (6, 4), (6, 3), (6, 2), (6, 6), (6, 24), (6, 28), (6, 27), (6, 21), (6, 30), (6, 29), (6, 23), (6, 22), (6, 26), (6, 25), (7, 0), (6, 31), (7, 6)]

attribute [local irreducible] destA17

set_option Elab.async false in
private theorem checkA17 : ∀ i : Fin 32,
    stepA (rows 17 i) = rows (destA17 i).1 (destA17 i).2 := by
  decide +kernel

private def destA18 : Fin 32 → Fin 24 × Fin 32 :=
  ![(7, 12), (7, 11), (7, 14), (7, 13), (7, 1), (6, 8), (6, 7), (6, 10), (6, 9), (7, 3), (7, 2), (7, 5), (7, 4), (7, 16), (7, 15), (7, 18), (7, 17), (5, 2), (2, 31), (2, 20), (2, 19), (2, 22), (2, 21), (3, 1), (3, 0), (3, 3), (3, 2), (3, 27), (3, 26), (3, 29), (3, 28), (2, 18)]

attribute [local irreducible] destA18

set_option Elab.async false in
private theorem checkA18 : ∀ i : Fin 32,
    stepA (rows 18 i) = rows (destA18 i).1 (destA18 i).2 := by
  decide +kernel

private def destA19 : Fin 32 → Fin 24 × Fin 32 :=
  ![(2, 24), (2, 23), (2, 26), (2, 25), (3, 7), (3, 11), (3, 10), (3, 4), (3, 13), (3, 12), (3, 6), (3, 5), (3, 9), (3, 8), (3, 15), (3, 14), (3, 30), (4, 2), (4, 1), (4, 0), (3, 31), (4, 3), (4, 22), (4, 21), (4, 24), (4, 23), (2, 28), (2, 27), (2, 30), (2, 29), (3, 16), (3, 20)]

attribute [local irreducible] destA19

set_option Elab.async false in
private theorem checkA19 : ∀ i : Fin 32,
    stepA (rows 19 i) = rows (destA19 i).1 (destA19 i).2 := by
  decide +kernel

private def destA20 : Fin 32 → Fin 24 × Fin 32 :=
  ![(3, 19), (3, 18), (3, 17), (3, 21), (4, 5), (4, 4), (4, 11), (4, 10), (4, 14), (4, 13), (4, 7), (4, 6), (4, 15), (4, 9), (4, 8), (4, 12), (4, 26), (4, 25), (4, 28), (4, 27), (5, 1), (3, 23), (3, 22), (3, 25), (3, 24), (4, 17), (4, 16), (4, 19), (4, 18), (4, 30), (4, 29), (5, 0)]

attribute [local irreducible] destA20

set_option Elab.async false in
private theorem checkA20 : ∀ i : Fin 32,
    stepA (rows 20 i) = rows (destA20 i).1 (destA20 i).2 := by
  decide +kernel

private def destA21 : Fin 32 → Fin 24 × Fin 32 :=
  ![(4, 31), (4, 20), (0, 3), (0, 2), (0, 8), (0, 7), (0, 13), (0, 5), (0, 4), (0, 10), (0, 9), (0, 15), (0, 14), (0, 6), (0, 12), (0, 11), (0, 31), (0, 30), (1, 1), (1, 0), (1, 11), (1, 10), (1, 13), (1, 12), (1, 22), (1, 26), (1, 25), (1, 24), (1, 23), (1, 27), (0, 17), (0, 16)]

attribute [local irreducible] destA21

set_option Elab.async false in
private theorem checkA21 : ∀ i : Fin 32,
    stepA (rows 21 i) = rows (destA21 i).1 (destA21 i).2 := by
  decide +kernel

private def destA22 : Fin 32 → Fin 24 × Fin 32 :=
  ![(0, 19), (0, 18), (1, 3), (1, 2), (1, 5), (1, 4), (1, 29), (1, 28), (1, 31), (1, 30), (0, 21), (0, 20), (0, 23), (0, 22), (1, 15), (1, 14), (1, 17), (1, 16), (2, 1), (2, 0), (2, 3), (2, 2), (0, 24), (0, 28), (0, 27), (0, 26), (0, 25), (0, 29), (1, 7), (1, 6), (1, 9), (1, 8)]

attribute [local irreducible] destA22

set_option Elab.async false in
private theorem checkA22 : ∀ i : Fin 32,
    stepA (rows 22 i) = rows (destA22 i).1 (destA22 i).2 := by
  decide +kernel

private def destA23 : Fin 32 → Fin 24 × Fin 32 :=
  ![(1, 19), (1, 18), (1, 21), (1, 20), (2, 8), (2, 7), (2, 13), (2, 5), (2, 4), (2, 10), (2, 9), (2, 15), (2, 14), (2, 6), (2, 12), (2, 11), (2, 17), (2, 16), (0, 1), (0, 0), (23, 19), (23, 18), (21, 3), (21, 2), (21, 8), (21, 7), (21, 13), (21, 5), (21, 4), (21, 10), (21, 9), (21, 15)]

attribute [local irreducible] destA23

set_option Elab.async false in
private theorem checkA23 : ∀ i : Fin 32,
    stepA (rows 23 i) = rows (destA23 i).1 (destA23 i).2 := by
  decide +kernel

theorem rows_mul_A (c : Fin 24) (i : Fin 32) :
    ∃ d j, rows c i ᵥ* matrixA = rows d j := by
  fin_cases c
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA0 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA1 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA2 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA3 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA4 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA5 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA6 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA7 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA8 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA9 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA10 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA11 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA12 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA13 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA14 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA15 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA16 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA17 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA18 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA19 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA20 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA21 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA22 i)⟩
  · exact ⟨_, _, (stepA_eq _).symm.trans (checkA23 i)⟩

private def destB0 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 6), (21, 31), (4, 26), (12, 31), (12, 9), (11, 17), (3, 11), (18, 3), (18, 0), (12, 30), (12, 27), (3, 20), (3, 16), (17, 17), (11, 3), (10, 31), (3, 19), (11, 2), (3, 3), (3, 0), (17, 26), (17, 22), (11, 18), (18, 1), (17, 25), (3, 10), (3, 7), (17, 16), (17, 13), (3, 1), (17, 6), (22, 15)]

attribute [local irreducible] destB0

set_option Elab.async false in
private theorem checkB0 : ∀ i : Fin 32,
    stepB (rows 0 i) = rows (destB0 i).1 (destB0 i).2 := by
  decide +kernel

private def destB1 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 29), (16, 20), (16, 28), (16, 25), (2, 20), (16, 18), (16, 15), (18, 17), (16, 26), (16, 19), (9, 2), (8, 30), (5, 8), (9, 8), (9, 5), (22, 7), (8, 31), (8, 25), (9, 1), (8, 24), (2, 18), (8, 15), (21, 27), (8, 10), (8, 5), (21, 23), (21, 21), (7, 30), (7, 22), (16, 7), (8, 0), (7, 29)]

attribute [local irreducible] destB1

set_option Elab.async false in
private theorem checkB1 : ∀ i : Fin 32,
    stepB (rows 1 i) = rows (destB1 i).1 (destB1 i).2 := by
  decide +kernel

private def destB2 : Fin 32 → Fin 24 × Fin 32 :=
  ![(21, 28), (21, 24), (16, 10), (21, 8), (16, 12), (16, 9), (8, 4), (21, 13), (21, 7), (16, 4), (16, 2), (7, 23), (7, 19), (21, 20), (16, 8), (16, 5), (16, 1), (21, 2), (18, 6), (14, 8), (20, 26), (13, 31), (13, 22), (13, 30), (13, 27), (0, 31), (13, 20), (13, 17), (18, 4), (13, 28), (13, 21), (11, 4)]

attribute [local irreducible] destB2

set_option Elab.async false in
private theorem checkB2 : ∀ i : Fin 32,
    stepB (rows 2 i) = rows (destB2 i).1 (destB2 i).2 := by
  decide +kernel

private def destB3 : Fin 32 → Fin 24 × Fin 32 :=
  ![(23, 13), (23, 8), (11, 20), (23, 1), (17, 27), (12, 6), (11, 19), (22, 25), (10, 13), (10, 8), (23, 3), (23, 0), (17, 18), (17, 15), (11, 5), (10, 28), (23, 7), (17, 28), (17, 19), (22, 26), (22, 22), (17, 10), (17, 12), (17, 9), (10, 7), (17, 14), (19, 11), (22, 9), (19, 20), (19, 16), (19, 19), (9, 3)]

attribute [local irreducible] destB3

set_option Elab.async false in
private theorem checkB3 : ∀ i : Fin 32,
    stepB (rows 3 i) = rows (destB3 i).1 (destB3 i).2 := by
  decide +kernel

private def destB4 : Fin 32 → Fin 24 × Fin 32 :=
  ![(8, 26), (19, 3), (19, 0), (8, 17), (22, 5), (22, 2), (19, 10), (19, 7), (8, 22), (8, 18), (22, 8), (22, 6), (8, 27), (22, 1), (21, 30), (19, 1), (8, 21), (22, 0), (8, 16), (8, 14), (22, 3), (21, 15), (21, 9), (18, 20), (21, 22), (21, 17), (23, 19), (21, 10), (21, 5), (21, 14), (21, 4), (16, 3)]

attribute [local irreducible] destB4

set_option Elab.async false in
private theorem checkB4 : ∀ i : Fin 32,
    stepB (rows 4 i) = rows (destB4 i).1 (destB4 i).2 := by
  decide +kernel

private def destB5 : Fin 32 → Fin 24 × Fin 32 :=
  ![(21, 3), (18, 18), (2, 28), (4, 14), (4, 10), (1, 15), (4, 20), (4, 17), (18, 14), (4, 11), (4, 5), (4, 13), (4, 4), (0, 1), (3, 27), (1, 7), (0, 27), (13, 0), (0, 23), (0, 21), (13, 8), (13, 13), (13, 7), (3, 25), (3, 23), (0, 28), (0, 24), (12, 3), (11, 22), (0, 8), (13, 1), (12, 24)]

attribute [local irreducible] destB5

set_option Elab.async false in
private theorem checkB5 : ∀ i : Fin 32,
    stepB (rows 5 i) = rows (destB5 i).1 (destB5 i).2 := by
  decide +kernel

private def destB6 : Fin 32 → Fin 24 × Fin 32 :=
  ![(3, 18), (3, 12), (0, 13), (0, 7), (3, 21), (3, 17), (0, 20), (3, 22), (11, 21), (3, 13), (3, 4), (10, 3), (10, 0), (2, 30), (9, 17), (17, 3), (9, 26), (9, 22), (17, 8), (17, 5), (10, 1), (9, 25), (2, 26), (2, 23), (17, 7), (2, 29), (2, 27), (16, 30), (16, 21), (9, 16), (9, 13), (2, 22)]

attribute [local irreducible] destB6

set_option Elab.async false in
private theorem checkB6 : ∀ i : Fin 32,
    stepB (rows 6 i) = rows (destB6 i).1 (destB6 i).2 := by
  decide +kernel

private def destB7 : Fin 32 → Fin 24 × Fin 32 :=
  ![(2, 19), (2, 21), (17, 2), (16, 31), (2, 24), (16, 22), (16, 13), (8, 13), (18, 28), (8, 12), (8, 2), (8, 11), (8, 6), (0, 2), (7, 31), (7, 26), (16, 11), (8, 7), (8, 1), (15, 30), (2, 13), (2, 8), (15, 26), (15, 24), (2, 1), (1, 25), (4, 27), (2, 3), (2, 0), (15, 31), (15, 27), (4, 30)]

attribute [local irreducible] destB7

set_option Elab.async false in
private theorem checkB7 : ∀ i : Fin 32,
    stepB (rows 7 i) = rows (destB7 i).1 (destB7 i).2 := by
  decide +kernel

private def destB8 : Fin 32 → Fin 24 × Fin 32 :=
  ![(15, 11), (5, 0), (4, 29), (2, 7), (15, 16), (15, 10), (4, 24), (4, 22), (1, 26), (1, 22), (15, 23), (4, 28), (4, 25), (4, 21), (14, 23), (18, 16), (15, 0), (14, 28), (14, 31), (4, 15), (4, 6), (14, 15), (14, 12), (3, 29), (18, 12), (18, 9), (14, 22), (14, 19), (4, 2), (3, 30), (18, 15), (18, 13)]

attribute [local irreducible] destB8

set_option Elab.async false in
private theorem checkB8 : ∀ i : Fin 32,
    stepB (rows 8 i) = rows (destB8 i).1 (destB8 i).2 := by
  decide +kernel

private def destB9 : Fin 32 → Fin 24 × Fin 32 :=
  ![(4, 7), (18, 8), (18, 5), (14, 13), (4, 1), (18, 7), (3, 28), (3, 26), (18, 10), (7, 5), (7, 2), (1, 9), (6, 19), (14, 5), (6, 28), (6, 24), (14, 10), (14, 7), (7, 3), (6, 27), (1, 5), (1, 2), (14, 9), (1, 8), (1, 6), (14, 0), (13, 23), (6, 18), (6, 15), (1, 1), (0, 30), (1, 0)]

attribute [local irreducible] destB9

set_option Elab.async false in
private theorem checkB9 : ∀ i : Fin 32,
    stepB (rows 9 i) = rows (destB9 i).1 (destB9 i).2 := by
  decide +kernel

private def destB10 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 4), (14, 1), (1, 3), (13, 24), (13, 15), (13, 9), (6, 8), (20, 14), (20, 10), (12, 5), (11, 27), (5, 31), (5, 22), (20, 20), (13, 3), (12, 26), (12, 10), (11, 25), (5, 30), (5, 27), (0, 15), (0, 9), (13, 2), (12, 28), (0, 22), (11, 7), (11, 0), (5, 20), (20, 17), (12, 22), (12, 13), (23, 16)]

attribute [local irreducible] destB10

set_option Elab.async false in
private theorem checkB10 : ∀ i : Fin 32,
    stepB (rows 10 i) = rows (destB10 i).1 (destB10 i).2 := by
  decide +kernel

private def destB11 : Fin 32 → Fin 24 × Fin 32 :=
  ![(13, 10), (13, 5), (23, 15), (23, 5), (20, 11), (20, 5), (11, 28), (11, 12), (12, 21), (12, 18), (0, 17), (13, 14), (13, 4), (3, 24), (10, 26), (10, 22), (5, 17), (23, 14), (23, 9), (20, 13), (20, 4), (17, 30), (17, 23), (12, 11), (12, 8), (12, 4), (11, 15), (11, 11), (11, 8), (5, 28), (5, 21), (3, 15)]

attribute [local irreducible] destB11

set_option Elab.async false in
private theorem checkB11 : ∀ i : Fin 32,
    stepB (rows 11 i) = rows (destB11 i).1 (destB11 i).2 := by
  decide +kernel

private def destB12 : Fin 32 → Fin 24 × Fin 32 :=
  ![(3, 6), (0, 10), (0, 5), (18, 2), (12, 29), (12, 25), (19, 27), (10, 15), (10, 5), (23, 2), (11, 1), (10, 30), (12, 7), (11, 23), (3, 14), (3, 8), (0, 14), (0, 4), (10, 14), (10, 9), (0, 3), (11, 6), (10, 29), (3, 2), (17, 31), (12, 19), (12, 12), (22, 29), (10, 23), (10, 17), (23, 10), (23, 4)]

attribute [local irreducible] destB12

set_option Elab.async false in
private theorem checkB12 : ∀ i : Fin 32,
    stepB (rows 12 i) = rows (destB12 i).1 (destB12 i).2 := by
  decide +kernel

private def destB13 : Fin 32 → Fin 24 × Fin 32 :=
  ![(17, 24), (17, 21), (11, 26), (11, 9), (10, 25), (10, 16), (2, 31), (17, 29), (17, 20), (11, 24), (11, 14), (3, 9), (3, 5), (17, 11), (10, 10), (10, 4), (9, 27), (22, 16), (9, 18), (9, 15), (22, 19), (22, 21), (22, 18), (17, 4), (17, 1), (9, 28), (9, 19), (22, 13), (22, 11), (9, 10), (22, 17), (22, 14)]

attribute [local irreducible] destB13

set_option Elab.async false in
private theorem checkB13 : ∀ i : Fin 32,
    stepB (rows 13 i) = rows (destB13 i).1 (destB13 i).2 := by
  decide +kernel

private def destB14 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 24), (16, 16), (9, 12), (9, 9), (16, 27), (16, 23), (9, 14), (17, 0), (22, 10), (16, 17), (16, 14), (5, 9), (19, 25), (19, 23), (5, 12), (19, 18), (9, 6), (5, 14), (5, 11), (19, 12), (5, 6), (5, 4), (19, 21), (19, 17), (9, 0), (8, 29), (5, 10), (5, 7), (19, 22), (9, 7), (9, 4), (19, 13)]

attribute [local irreducible] destB14

set_option Elab.async false in
private theorem checkB14 : ∀ i : Fin 32,
    stepB (rows 14 i) = rows (destB14 i).1 (destB14 i).2 := by
  decide +kernel

private def destB15 : Fin 32 → Fin 24 × Fin 32 :=
  ![(19, 4), (8, 20), (8, 23), (8, 19), (5, 3), (8, 28), (18, 30), (18, 26), (18, 23), (7, 28), (21, 29), (21, 25), (18, 29), (18, 27), (8, 9), (8, 3), (21, 12), (18, 22), (18, 19), (8, 8), (18, 21), (7, 24), (7, 20), (21, 19), (21, 16), (18, 24), (21, 26), (21, 18), (7, 27), (7, 25), (21, 11), (21, 6)]

attribute [local irreducible] destB15

set_option Elab.async false in
private theorem checkB15 : ∀ i : Fin 32,
    stepB (rows 15 i) = rows (destB15 i).1 (destB15 i).2 := by
  decide +kernel

private def destB16 : Fin 32 → Fin 24 × Fin 32 :=
  ![(7, 21), (15, 18), (15, 12), (7, 8), (15, 25), (15, 20), (23, 17), (15, 13), (15, 8), (15, 17), (15, 7), (4, 23), (15, 6), (7, 6), (6, 29), (20, 27), (6, 20), (6, 17), (20, 30), (21, 0), (20, 29), (14, 6), (14, 3), (6, 30), (6, 21), (20, 24), (20, 22), (6, 12), (20, 28), (20, 25), (13, 26), (13, 18)]

attribute [local irreducible] destB16

set_option Elab.async false in
private theorem checkB16 : ∀ i : Fin 32,
    stepB (rows 16 i) = rows (destB16 i).1 (destB16 i).2 := by
  decide +kernel

private def destB17 : Fin 32 → Fin 24 × Fin 32 :=
  ![(6, 14), (6, 11), (13, 29), (13, 25), (6, 16), (14, 2), (20, 21), (13, 19), (13, 16), (20, 15), (20, 6), (11, 30), (19, 29), (22, 31), (20, 2), (19, 30), (23, 12), (23, 6), (20, 7), (20, 1), (10, 27), (10, 18), (23, 11), (11, 29), (11, 16), (22, 27), (22, 23), (19, 28), (19, 26), (10, 12), (10, 6), (10, 11)]

attribute [local irreducible] destB17

set_option Elab.async false in
private theorem checkB17 : ∀ i : Fin 32,
    stepB (rows 17 i) = rows (destB17 i).1 (destB17 i).2 := by
  decide +kernel

private def destB18 : Fin 32 → Fin 24 × Fin 32 :=
  ![(22, 30), (22, 28), (10, 19), (22, 24), (22, 12), (19, 24), (23, 18), (19, 15), (19, 6), (19, 14), (19, 8), (5, 5), (19, 2), (18, 31), (22, 4), (19, 9), (19, 5), (20, 23), (5, 1), (2, 16), (7, 16), (2, 15), (2, 5), (2, 14), (2, 9), (0, 0), (2, 2), (1, 29), (4, 31), (2, 10), (2, 4), (1, 16)]

attribute [local irreducible] destB18

set_option Elab.async false in
private theorem checkB18 : ∀ i : Fin 32,
    stepB (rows 18 i) = rows (destB18 i).1 (destB18 i).2 := by
  decide +kernel

private def destB19 : Fin 32 → Fin 24 × Fin 32 :=
  ![(15, 5), (15, 3), (1, 19), (14, 30), (4, 18), (1, 21), (1, 18), (14, 24), (1, 13), (1, 11), (15, 1), (14, 29), (4, 12), (4, 9), (1, 17), (1, 14), (15, 2), (4, 19), (4, 16), (14, 25), (14, 16), (4, 0), (4, 3), (3, 31), (1, 10), (4, 8), (6, 5), (13, 12), (6, 10), (6, 7), (6, 9), (0, 29)]

attribute [local irreducible] destB19

set_option Elab.async false in
private theorem checkB19 : ∀ i : Fin 32,
    stepB (rows 19 i) = rows (destB19 i).1 (destB19 i).2 := by
  decide +kernel

private def destB20 : Fin 32 → Fin 24 × Fin 32 :=
  ![(0, 25), (6, 0), (5, 23), (0, 12), (12, 23), (12, 14), (6, 4), (6, 1), (0, 19), (0, 16), (13, 11), (13, 6), (0, 26), (12, 0), (11, 13), (5, 24), (0, 18), (11, 31), (0, 11), (0, 6), (12, 15), (9, 30), (9, 23), (5, 15), (10, 2), (9, 31), (22, 20), (9, 24), (9, 21), (9, 29), (9, 20), (2, 25)]

attribute [local irreducible] destB20

set_option Elab.async false in
private theorem checkB20 : ∀ i : Fin 32,
    stepB (rows 20 i) = rows (destB20 i).1 (destB20 i).2 := by
  decide +kernel

private def destB21 : Fin 32 → Fin 24 × Fin 32 :=
  ![(9, 11), (5, 13), (2, 17), (7, 18), (7, 14), (7, 11), (1, 31), (16, 0), (15, 28), (7, 17), (7, 15), (2, 12), (2, 6), (15, 15), (7, 10), (7, 7), (2, 11), (7, 9), (1, 27), (1, 23), (15, 22), (15, 19), (7, 12), (15, 29), (15, 21), (1, 30), (1, 28), (15, 14), (15, 9), (1, 24), (15, 4), (21, 1)]

attribute [local irreducible] destB21

set_option Elab.async false in
private theorem checkB21 : ∀ i : Fin 32,
    stepB (rows 21 i) = rows (destB21 i).1 (destB21 i).2 := by
  decide +kernel

private def destB22 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 27), (14, 18), (14, 26), (14, 20), (1, 12), (14, 14), (14, 11), (18, 11), (14, 21), (14, 17), (7, 0), (6, 25), (5, 2), (7, 4), (7, 1), (20, 31), (6, 26), (6, 23), (6, 31), (6, 22), (1, 4), (6, 13), (20, 18), (6, 6), (6, 3), (20, 12), (20, 9), (5, 26), (5, 18), (12, 1), (5, 29), (5, 25)]

attribute [local irreducible] destB22

set_option Elab.async false in
private theorem checkB22 : ∀ i : Fin 32,
    stepB (rows 22 i) = rows (destB22 i).1 (destB22 i).2 := by
  decide +kernel

private def destB23 : Fin 32 → Fin 24 × Fin 32 :=
  ![(20, 19), (20, 16), (12, 17), (20, 0), (12, 20), (12, 16), (6, 2), (20, 3), (19, 31), (10, 24), (10, 21), (5, 19), (5, 16), (20, 8), (12, 2), (11, 10), (10, 20), (18, 25), (1, 20), (7, 13), (16, 6), (21, 31), (4, 26), (12, 31), (12, 9), (11, 17), (3, 11), (18, 3), (18, 0), (12, 30), (12, 27), (3, 20)]

attribute [local irreducible] destB23

set_option Elab.async false in
private theorem checkB23 : ∀ i : Fin 32,
    stepB (rows 23 i) = rows (destB23 i).1 (destB23 i).2 := by
  decide +kernel

theorem rows_mul_B (c : Fin 24) (i : Fin 32) :
    ∃ d j, rows c i ᵥ* matrixB = rows d j := by
  fin_cases c
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB0 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB1 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB2 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB3 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB4 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB5 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB6 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB7 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB8 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB9 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB10 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB11 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB12 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB13 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB14 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB15 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB16 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB17 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB18 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB19 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB20 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB21 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB22 i)⟩
  · exact ⟨_, _, (stepB_eq _).symm.trans (checkB23 i)⟩

private def destBInv0 : Fin 32 → Fin 24 × Fin 32 :=
  ![(18, 25), (5, 13), (7, 13), (12, 20), (12, 17), (12, 2), (20, 19), (6, 3), (5, 29), (10, 21), (12, 1), (20, 18), (20, 3), (6, 2), (12, 16), (10, 20), (20, 9), (11, 10), (20, 16), (20, 8), (6, 6), (5, 19), (10, 24), (5, 18), (5, 26), (20, 0), (20, 12), (5, 16), (5, 25), (19, 31), (9, 30), (2, 25)]

attribute [local irreducible] destBInv0

set_option Elab.async false in
private theorem checkBInv0 : ∀ i : Fin 32,
    stepBInv (rows 0 i) = rows (destBInv0 i).1 (destBInv0 i).2 := by
  decide +kernel

private def destBInv1 : Fin 32 → Fin 24 × Fin 32 :=
  ![(9, 31), (9, 29), (9, 21), (10, 2), (22, 20), (9, 20), (9, 24), (5, 15), (9, 23), (9, 11), (19, 24), (19, 9), (22, 4), (19, 8), (19, 15), (5, 5), (18, 31), (19, 14), (19, 6), (19, 2), (23, 18), (19, 5), (8, 9), (21, 19), (21, 29), (7, 25), (8, 8), (21, 18), (21, 26), (18, 27), (21, 25), (21, 6)]

attribute [local irreducible] destBInv1

set_option Elab.async false in
private theorem checkBInv1 : ∀ i : Fin 32,
    stepBInv (rows 1 i) = rows (destBInv1 i).1 (destBInv1 i).2 := by
  decide +kernel

private def destBInv2 : Fin 32 → Fin 24 × Fin 32 :=
  ![(7, 28), (7, 24), (18, 26), (7, 27), (18, 30), (18, 22), (21, 12), (8, 3), (7, 21), (18, 24), (18, 29), (21, 16), (21, 11), (7, 20), (18, 23), (18, 21), (18, 19), (21, 2), (1, 20), (7, 0), (1, 4), (7, 1), (6, 31), (6, 23), (7, 4), (20, 31), (6, 22), (6, 26), (5, 2), (6, 25), (6, 13), (13, 6)]

attribute [local irreducible] destBInv2

set_option Elab.async false in
private theorem checkBInv2 : ∀ i : Fin 32,
    stepBInv (rows 2 i) = rows (destBInv2 i).1 (destBInv2 i).2 := by
  decide +kernel

private def destBInv3 : Fin 32 → Fin 24 × Fin 32 :=
  ![(0, 19), (0, 29), (12, 23), (0, 18), (6, 10), (13, 12), (12, 0), (0, 26), (12, 15), (13, 11), (0, 25), (0, 6), (6, 1), (6, 9), (12, 14), (11, 31), (0, 12), (6, 5), (6, 0), (0, 16), (0, 11), (6, 4), (6, 7), (5, 24), (11, 13), (5, 23), (9, 7), (5, 14), (9, 6), (8, 23), (8, 29), (19, 23)]

attribute [local irreducible] destBInv3

set_option Elab.async false in
private theorem checkBInv3 : ∀ i : Fin 32,
    stepBInv (rows 3 i) = rows (destBInv3 i).1 (destBInv3 i).2 := by
  decide +kernel

private def destBInv4 : Fin 32 → Fin 24 × Fin 32 :=
  ![(19, 21), (9, 4), (8, 28), (19, 22), (5, 12), (5, 10), (8, 20), (9, 0), (19, 25), (19, 13), (5, 4), (5, 9), (19, 12), (5, 11), (5, 3), (8, 19), (19, 18), (5, 7), (19, 4), (19, 17), (5, 6), (8, 13), (8, 7), (16, 11), (8, 6), (8, 12), (0, 2), (7, 26), (8, 11), (8, 2), (7, 31), (18, 28)]

attribute [local irreducible] destBInv4

set_option Elab.async false in
private theorem checkBInv4 : ∀ i : Fin 32,
    stepBInv (rows 4 i) = rows (destBInv4 i).1 (destBInv4 i).2 := by
  decide +kernel

private def destBInv5 : Fin 32 → Fin 24 × Fin 32 :=
  ![(8, 1), (18, 18), (22, 12), (15, 4), (14, 21), (18, 11), (14, 20), (14, 27), (1, 12), (14, 11), (14, 26), (14, 18), (14, 14), (21, 1), (14, 17), (20, 23), (23, 12), (11, 16), (22, 28), (23, 11), (10, 27), (11, 30), (10, 12), (20, 2), (20, 15), (22, 31), (22, 27), (10, 19), (11, 29), (22, 30), (10, 18), (10, 11)]

attribute [local irreducible] destBInv5

set_option Elab.async false in
private theorem checkBInv5 : ∀ i : Fin 32,
    stepBInv (rows 5 i) = rows (destBInv5 i).1 (destBInv5 i).2 := by
  decide +kernel

private def destBInv6 : Fin 32 → Fin 24 × Fin 32 :=
  ![(20, 1), (20, 7), (23, 6), (22, 24), (20, 6), (19, 26), (22, 23), (19, 29), (10, 6), (19, 30), (19, 28), (17, 1), (16, 27), (22, 21), (17, 0), (9, 28), (17, 4), (16, 17), (9, 27), (9, 12), (16, 16), (16, 24), (22, 19), (22, 17), (9, 15), (22, 11), (22, 16), (9, 19), (9, 14), (16, 14), (16, 23), (22, 18)]

attribute [local irreducible] destBInv6

set_option Elab.async false in
private theorem checkBInv6 : ∀ i : Fin 32,
    stepBInv (rows 6 i) = rows (destBInv6 i).1 (destBInv6 i).2 := by
  decide +kernel

private def destBInv7 : Fin 32 → Fin 24 × Fin 32 :=
  ![(22, 10), (22, 14), (9, 10), (9, 18), (22, 13), (9, 9), (16, 13), (21, 15), (16, 3), (21, 17), (21, 14), (21, 5), (21, 22), (23, 19), (21, 4), (21, 10), (18, 20), (21, 9), (21, 3), (2, 12), (15, 22), (16, 0), (1, 28), (2, 11), (15, 21), (15, 29), (7, 15), (15, 28), (15, 9), (1, 31), (1, 27), (7, 14)]

attribute [local irreducible] destBInv7

set_option Elab.async false in
private theorem checkBInv7 : ∀ i : Fin 32,
    stepBInv (rows 7 i) = rows (destBInv7 i).1 (destBInv7 i).2 := by
  decide +kernel

private def destBInv8 : Fin 32 → Fin 24 × Fin 32 :=
  ![(1, 30), (7, 18), (7, 10), (15, 15), (2, 6), (1, 24), (7, 12), (7, 17), (15, 19), (15, 14), (1, 23), (7, 11), (7, 9), (7, 7), (4, 19), (1, 21), (4, 18), (4, 3), (4, 9), (15, 3), (15, 1), (4, 16), (4, 8), (15, 2), (1, 19), (1, 17), (4, 0), (4, 12), (15, 5), (14, 25), (1, 11), (1, 16)]

attribute [local irreducible] destBInv8

set_option Elab.async false in
private theorem checkBInv8 : ∀ i : Fin 32,
    stepBInv (rows 8 i) = rows (destBInv8 i).1 (destBInv8 i).2 := by
  decide +kernel

private def destBInv9 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 24), (1, 18), (1, 10), (3, 31), (14, 30), (1, 14), (14, 16), (14, 29), (1, 13), (14, 3), (13, 29), (21, 0), (14, 2), (6, 30), (14, 6), (13, 19), (6, 29), (6, 14), (13, 18), (13, 26), (20, 30), (20, 28), (6, 17), (20, 22), (20, 27), (6, 21), (6, 16), (13, 16), (13, 25), (20, 29), (20, 21), (20, 25)]

attribute [local irreducible] destBInv9

set_option Elab.async false in
private theorem checkBInv9 : ∀ i : Fin 32,
    stepBInv (rows 9 i) = rows (destBInv9 i).1 (destBInv9 i).2 := by
  decide +kernel

private def destBInv10 : Fin 32 → Fin 24 × Fin 32 :=
  ![(6, 12), (6, 20), (20, 24), (6, 11), (13, 15), (12, 8), (17, 30), (3, 24), (3, 9), (12, 19), (13, 14), (17, 31), (17, 29), (3, 8), (12, 18), (12, 7), (13, 5), (12, 29), (17, 21), (18, 2), (23, 16), (23, 10), (11, 15), (12, 28), (23, 9), (13, 4), (11, 14), (17, 20), (3, 15), (12, 22), (12, 11), (0, 15)]

attribute [local irreducible] destBInv10

set_option Elab.async false in
private theorem checkBInv10 : ∀ i : Fin 32,
    stepBInv (rows 10 i) = rows (destBInv10 i).1 (destBInv10 i).2 := by
  decide +kernel

private def destBInv11 : Fin 32 → Fin 24 × Fin 32 :=
  ![(10, 26), (12, 10), (0, 17), (0, 14), (2, 31), (3, 14), (12, 21), (10, 25), (11, 28), (13, 3), (23, 15), (11, 27), (11, 7), (20, 14), (13, 10), (11, 26), (17, 24), (0, 5), (0, 22), (3, 6), (3, 2), (6, 8), (5, 28), (12, 13), (13, 9), (10, 17), (13, 2), (10, 10), (11, 6), (17, 23), (17, 11), (20, 17)]

attribute [local irreducible] destBInv11

set_option Elab.async false in
private theorem checkBInv11 : ∀ i : Fin 32,
    stepBInv (rows 11 i) = rows (destBInv11 i).1 (destBInv11 i).2 := by
  decide +kernel

private def destBInv12 : Fin 32 → Fin 24 × Fin 32 :=
  ![(20, 13), (22, 29), (23, 14), (5, 27), (11, 25), (10, 9), (3, 5), (12, 12), (11, 24), (0, 4), (10, 16), (11, 23), (12, 26), (10, 30), (20, 5), (20, 20), (23, 5), (23, 2), (11, 9), (12, 25), (23, 4), (11, 8), (10, 29), (20, 4), (5, 31), (12, 5), (10, 15), (0, 10), (10, 23), (12, 4), (0, 9), (0, 3)]

attribute [local irreducible] destBInv12

set_option Elab.async false in
private theorem checkBInv12 : ∀ i : Fin 32,
    stepBInv (rows 12 i) = rows (destBInv12 i).1 (destBInv12 i).2 := by
  decide +kernel

private def destBInv13 : Fin 32 → Fin 24 × Fin 32 :=
  ![(5, 17), (5, 30), (10, 22), (10, 14), (11, 12), (11, 1), (20, 11), (5, 22), (5, 20), (10, 5), (11, 0), (20, 10), (19, 27), (5, 21), (11, 11), (10, 4), (17, 8), (2, 27), (16, 31), (17, 7), (2, 26), (2, 30), (2, 22), (9, 26), (10, 3), (17, 3), (16, 30), (2, 24), (2, 29), (17, 2), (2, 23), (2, 21)]

attribute [local irreducible] destBInv13

set_option Elab.async false in
private theorem checkBInv13 : ∀ i : Fin 32,
    stepBInv (rows 13 i) = rows (destBInv13 i).1 (destBInv13 i).2 := by
  decide +kernel

private def destBInv14 : Fin 32 → Fin 24 × Fin 32 :=
  ![(9, 25), (10, 1), (17, 5), (16, 22), (10, 0), (9, 13), (16, 21), (9, 17), (2, 19), (9, 22), (9, 16), (22, 6), (8, 22), (9, 3), (22, 5), (8, 21), (19, 20), (22, 9), (22, 1), (8, 27), (22, 3), (22, 8), (8, 26), (8, 14), (19, 7), (19, 19), (22, 2), (22, 0), (8, 17), (19, 11), (19, 3), (8, 18)]

attribute [local irreducible] destBInv14

set_option Elab.async false in
private theorem checkBInv14 : ∀ i : Fin 32,
    stepBInv (rows 14 i) = rows (destBInv14 i).1 (destBInv14 i).2 := by
  decide +kernel

private def destBInv15 : Fin 32 → Fin 24 × Fin 32 :=
  ![(8, 16), (19, 10), (19, 16), (19, 1), (21, 30), (19, 0), (16, 12), (16, 10), (16, 8), (21, 28), (8, 5), (8, 0), (16, 2), (16, 7), (21, 27), (21, 13), (8, 4), (16, 9), (16, 1), (21, 21), (16, 5), (21, 24), (21, 20), (8, 10), (7, 23), (16, 4), (7, 22), (7, 30), (21, 8), (21, 23), (7, 19), (7, 29)]

attribute [local irreducible] destBInv15

set_option Elab.async false in
private theorem checkBInv15 : ∀ i : Fin 32,
    stepBInv (rows 15 i) = rows (destBInv15 i).1 (destBInv15 i).2 := by
  decide +kernel

private def destBInv16 : Fin 32 → Fin 24 × Fin 32 :=
  ![(21, 7), (2, 16), (2, 10), (4, 31), (2, 9), (2, 15), (0, 0), (1, 29), (2, 14), (2, 5), (2, 2), (7, 16), (2, 4), (7, 6), (14, 10), (1, 6), (14, 1), (14, 9), (1, 5), (1, 9), (1, 1), (6, 28), (7, 5), (14, 5), (14, 0), (1, 3), (1, 8), (14, 4), (1, 2), (1, 0), (6, 27), (7, 3)]

attribute [local irreducible] destBInv16

set_option Elab.async false in
private theorem checkBInv16 : ∀ i : Fin 32,
    stepBInv (rows 16 i) = rows (destBInv16 i).1 (destBInv16 i).2 := by
  decide +kernel

private def destBInv17 : Fin 32 → Fin 24 × Fin 32 :=
  ![(14, 7), (13, 24), (7, 2), (6, 15), (13, 23), (6, 19), (0, 30), (6, 24), (6, 18), (3, 23), (3, 21), (13, 13), (3, 22), (0, 28), (3, 25), (3, 13), (0, 27), (0, 13), (3, 12), (3, 18), (13, 8), (13, 1), (0, 21), (11, 22), (13, 0), (0, 24), (0, 20), (3, 4), (3, 17), (13, 7), (11, 21), (12, 24)]

attribute [local irreducible] destBInv17

set_option Elab.async false in
private theorem checkBInv17 : ∀ i : Fin 32,
    stepBInv (rows 17 i) = rows (destBInv17 i).1 (destBInv17 i).2 := by
  decide +kernel

private def destBInv18 : Fin 32 → Fin 24 × Fin 32 :=
  ![(0, 8), (0, 23), (12, 3), (0, 7), (2, 28), (9, 2), (2, 18), (9, 5), (9, 1), (8, 25), (9, 8), (22, 7), (8, 24), (8, 31), (5, 8), (8, 30), (8, 15), (1, 7), (5, 1), (15, 18), (4, 23), (15, 20), (15, 17), (15, 8), (15, 25), (23, 17), (15, 7), (15, 13), (7, 8), (15, 12), (15, 6), (18, 13)]

attribute [local irreducible] destBInv18

set_option Elab.async false in
private theorem checkBInv18 : ∀ i : Fin 32,
    stepBInv (rows 18 i) = rows (destBInv18 i).1 (destBInv18 i).2 := by
  decide +kernel

private def destBInv19 : Fin 32 → Fin 24 × Fin 32 :=
  ![(4, 2), (4, 15), (18, 12), (4, 1), (15, 0), (18, 16), (18, 8), (4, 7), (18, 10), (18, 15), (4, 6), (3, 26), (14, 19), (14, 31), (18, 9), (18, 7), (3, 29), (14, 23), (14, 15), (3, 30), (3, 28), (14, 22), (14, 28), (14, 13), (18, 5), (14, 12), (17, 28), (12, 6), (17, 27), (17, 12), (17, 15), (23, 8)]

attribute [local irreducible] destBInv19

set_option Elab.async false in
private theorem checkBInv19 : ∀ i : Fin 32,
    stepBInv (rows 19 i) = rows (destBInv19 i).1 (destBInv19 i).2 := by
  decide +kernel

private def destBInv20 : Fin 32 → Fin 24 × Fin 32 :=
  ![(23, 3), (17, 19), (17, 14), (23, 7), (11, 20), (11, 5), (17, 10), (17, 18), (23, 13), (22, 26), (10, 8), (11, 4), (22, 25), (11, 19), (10, 7), (17, 9), (23, 1), (10, 28), (22, 22), (23, 0), (10, 13), (17, 6), (16, 26), (18, 17), (16, 25), (16, 29), (2, 20), (16, 15), (16, 28), (16, 20), (16, 18), (22, 15)]

attribute [local irreducible] destBInv20

set_option Elab.async false in
private theorem checkBInv20 : ∀ i : Fin 32,
    stepBInv (rows 20 i) = rows (destBInv20 i).1 (destBInv20 i).2 := by
  decide +kernel

private def destBInv21 : Fin 32 → Fin 24 × Fin 32 :=
  ![(16, 19), (21, 31), (2, 17), (5, 0), (4, 30), (4, 28), (15, 31), (2, 8), (2, 3), (4, 22), (4, 27), (15, 30), (15, 16), (2, 7), (4, 29), (4, 21), (15, 24), (4, 25), (15, 27), (15, 23), (2, 13), (1, 26), (4, 24), (1, 25), (2, 1), (15, 11), (15, 26), (1, 22), (2, 0), (15, 10), (4, 14), (0, 1)]

attribute [local irreducible] destBInv21

set_option Elab.async false in
private theorem checkBInv21 : ∀ i : Fin 32,
    stepBInv (rows 21 i) = rows (destBInv21 i).1 (destBInv21 i).2 := by
  decide +kernel

private def destBInv22 : Fin 32 → Fin 24 × Fin 32 :=
  ![(4, 17), (4, 13), (4, 5), (4, 20), (18, 14), (4, 4), (4, 11), (1, 15), (4, 10), (3, 27), (14, 8), (13, 28), (18, 4), (13, 27), (13, 31), (0, 31), (13, 17), (13, 30), (13, 22), (13, 20), (20, 26), (13, 21), (3, 20), (17, 26), (18, 3), (3, 7), (3, 19), (17, 25), (18, 1), (12, 27), (18, 0), (17, 13)]

attribute [local irreducible] destBInv22

set_option Elab.async false in
private theorem checkBInv22 : ∀ i : Fin 32,
    stepBInv (rows 22 i) = rows (destBInv22 i).1 (destBInv22 i).2 := by
  decide +kernel

private def destBInv23 : Fin 32 → Fin 24 × Fin 32 :=
  ![(3, 11), (3, 3), (12, 9), (3, 10), (12, 31), (11, 3), (17, 17), (3, 16), (3, 1), (11, 18), (12, 30), (17, 22), (17, 16), (3, 0), (11, 17), (11, 2), (10, 31), (16, 6), (18, 6), (4, 26), (18, 25), (5, 13), (7, 13), (12, 20), (12, 17), (12, 2), (20, 19), (6, 3), (5, 29), (10, 21), (12, 1), (20, 18)]

attribute [local irreducible] destBInv23

set_option Elab.async false in
private theorem checkBInv23 : ∀ i : Fin 32,
    stepBInv (rows 23 i) = rows (destBInv23 i).1 (destBInv23 i).2 := by
  decide +kernel

theorem rows_mul_BInv (c : Fin 24) (i : Fin 32) :
    ∃ d j, rows c i ᵥ* matrixBInv = rows d j := by
  fin_cases c
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv0 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv1 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv2 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv3 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv4 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv5 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv6 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv7 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv8 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv9 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv10 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv11 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv12 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv13 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv14 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv15 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv16 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv17 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv18 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv19 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv20 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv21 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv22 i)⟩
  · exact ⟨_, _, (stepBInv_eq _).symm.trans (checkBInv23 i)⟩

set_option Elab.async false in
private theorem fibre0 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 0 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 0 i = basisRow j ∨ rows 0 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre1 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 1 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 1 i = basisRow j ∨ rows 1 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre2 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 2 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 2 i = basisRow j ∨ rows 2 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre3 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 3 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 3 i = basisRow j ∨ rows 3 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre4 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 4 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 4 i = basisRow j ∨ rows 4 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre5 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 5 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 5 i = basisRow j ∨ rows 5 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre6 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 6 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 6 i = basisRow j ∨ rows 6 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre7 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 7 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 7 i = basisRow j ∨ rows 7 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre8 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 8 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 8 i = basisRow j ∨ rows 8 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre9 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 9 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 9 i = basisRow j ∨ rows 9 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre10 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 10 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 10 i = basisRow j ∨ rows 10 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre11 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 11 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 11 i = basisRow j ∨ rows 11 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre12 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 12 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 12 i = basisRow j ∨ rows 12 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre13 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 13 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 13 i = basisRow j ∨ rows 13 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre14 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 14 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 14 i = basisRow j ∨ rows 14 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre15 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 15 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 15 i = basisRow j ∨ rows 15 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre16 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 16 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 16 i = basisRow j ∨ rows 16 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre17 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 17 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 17 i = basisRow j ∨ rows 17 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre18 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 18 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 18 i = basisRow j ∨ rows 18 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre19 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 19 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 19 i = basisRow j ∨ rows 19 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre20 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 20 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 20 i = basisRow j ∨ rows 20 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre21 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 21 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 21 i = basisRow j ∨ rows 21 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre22 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 22 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 22 i = basisRow j ∨ rows 22 i = -basisRow j := by decide +kernel

set_option Elab.async false in
private theorem fibre23 : ∀ (i : Fin 32) (j : Fin 6),
    (fun k => reductionScalars (rows 23 i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows 23 i = basisRow j ∨ rows 23 i = -basisRow j := by decide +kernel

theorem rows_basis_fibre (c : Fin 24) (i : Fin 32) (j : Fin 6) :
    (fun k => reductionScalars (rows c i k)) = (fun k => reductionScalars (basisRow j k)) →
      rows c i = basisRow j ∨ rows c i = -basisRow j := by
  fin_cases c
  · exact fibre0 i j
  · exact fibre1 i j
  · exact fibre2 i j
  · exact fibre3 i j
  · exact fibre4 i j
  · exact fibre5 i j
  · exact fibre6 i j
  · exact fibre7 i j
  · exact fibre8 i j
  · exact fibre9 i j
  · exact fibre10 i j
  · exact fibre11 i j
  · exact fibre12 i j
  · exact fibre13 i j
  · exact fibre14 i j
  · exact fibre15 i j
  · exact fibre16 i j
  · exact fibre17 i j
  · exact fibre18 i j
  · exact fibre19 i j
  · exact fibre20 i j
  · exact fibre21 i j
  · exact fibre22 i j
  · exact fibre23 i j

theorem basisRow_eq_rows : ∀ j : Fin 6,
    basisRow j = rows (basisIndex j).1 (basisIndex j).2 := by decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.IntegralKernel
