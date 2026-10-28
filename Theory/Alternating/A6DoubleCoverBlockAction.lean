module

public import Theory.Alternating.A6DoubleCover
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- BEGIN Theory.A6DoubleCoverBlockAction -/
open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5

open FiberAction SchurPresentation
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

@[reducible, expose] public def a6DoubleCoverBlockIndex : Fin 144 → Fin 6 := fun i => Vector.get #v[
  0, 1, 2, 2, 3, 0, 3, 4, 3, 0, 1, 4, 3, 5, 4, 3, 0, 1, 2, 5, 4, 4,
  3, 5, 5, 4, 4, 0, 1, 2, 2, 3, 0, 1, 5, 5, 5, 4, 4, 5, 1, 5, 4, 4, 0, 1, 2,
  2, 3, 0, 3, 0, 1, 2, 1, 5, 5, 1, 5, 5, 4, 5, 4, 1, 2, 2, 5, 5, 4, 1, 2, 2,
  3, 0, 3, 4, 3, 1, 4, 0, 1, 2, 0, 2, 2, 5, 1, 5, 5, 4, 2, 0, 3, 0, 1, 1, 5,
  2, 3, 0, 3, 1, 4, 4, 3, 4, 0, 1, 2, 2, 3, 0, 0, 3, 0, 2, 5, 1, 5, 3, 0, 1,
  4, 3, 0, 2, 5, 3, 0, 1, 3, 4, 4, 2, 2, 1, 4, 3, 0, 5, 3, 1, 0, 2] i

@[reducible, expose] public def a6DoubleCoverQuotientGen1 : Equiv.Perm (Fin 6) :=
  List.formPerm [1, 2, 3, 4, 5]
@[reducible, expose] public def a6DoubleCoverQuotientGen2 : Equiv.Perm (Fin 6) :=
  List.formPerm [0, 1, 2]

private theorem a6DoubleCoverBlockIndex_gen1_case0 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (0 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (0 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case1 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (1 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (1 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case2 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (2 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (2 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case3 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (3 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (3 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case4 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (4 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (4 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case5 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (5 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (5 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case6 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (6 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (6 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case7 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (7 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (7 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case8 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (8 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (8 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case9 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (9 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (9 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case10 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (10 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (10 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case11 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (11 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (11 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case12 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (12 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (12 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case13 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (13 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (13 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case14 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (14 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (14 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case15 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (15 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (15 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case16 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (16 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (16 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case17 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (17 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (17 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case18 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (18 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (18 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case19 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (19 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (19 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case20 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (20 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (20 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case21 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (21 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (21 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case22 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (22 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (22 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case23 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (23 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (23 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case24 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (24 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (24 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case25 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (25 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (25 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case26 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (26 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (26 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case27 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (27 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (27 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case28 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (28 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (28 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case29 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (29 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (29 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case30 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (30 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (30 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case31 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (31 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (31 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case32 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (32 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (32 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case33 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (33 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (33 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case34 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (34 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (34 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case35 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (35 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (35 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case36 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (36 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (36 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case37 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (37 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (37 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case38 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (38 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (38 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case39 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (39 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (39 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case40 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (40 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (40 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case41 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (41 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (41 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case42 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (42 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (42 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case43 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (43 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (43 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case44 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (44 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (44 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case45 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (45 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (45 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case46 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (46 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (46 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case47 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (47 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (47 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case48 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (48 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (48 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case49 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (49 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (49 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case50 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (50 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (50 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case51 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (51 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (51 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case52 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (52 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (52 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case53 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (53 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (53 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case54 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (54 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (54 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case55 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (55 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (55 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case56 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (56 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (56 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case57 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (57 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (57 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case58 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (58 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (58 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case59 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (59 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (59 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case60 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (60 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (60 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case61 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (61 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (61 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case62 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (62 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (62 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case63 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (63 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (63 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case64 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (64 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (64 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case65 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (65 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (65 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case66 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (66 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (66 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case67 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (67 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (67 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case68 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (68 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (68 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case69 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (69 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (69 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case70 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (70 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (70 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case71 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (71 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (71 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case72 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (72 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (72 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case73 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (73 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (73 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case74 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (74 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (74 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case75 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (75 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (75 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case76 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (76 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (76 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case77 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (77 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (77 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case78 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (78 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (78 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case79 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (79 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (79 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case80 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (80 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (80 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case81 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (81 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (81 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case82 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (82 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (82 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case83 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (83 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (83 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case84 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (84 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (84 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case85 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (85 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (85 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case86 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (86 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (86 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case87 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (87 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (87 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case88 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (88 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (88 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case89 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (89 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (89 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case90 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (90 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (90 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case91 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (91 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (91 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case92 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (92 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (92 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case93 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (93 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (93 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case94 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (94 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (94 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case95 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (95 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (95 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case96 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (96 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (96 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case97 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (97 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (97 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case98 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (98 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (98 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case99 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (99 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (99 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case100 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (100 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (100 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case101 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (101 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (101 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case102 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (102 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (102 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case103 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (103 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (103 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case104 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (104 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (104 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case105 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (105 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (105 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case106 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (106 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (106 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case107 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (107 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (107 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case108 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (108 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (108 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case109 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (109 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (109 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case110 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (110 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (110 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case111 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (111 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (111 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case112 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (112 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (112 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case113 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (113 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (113 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case114 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (114 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (114 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case115 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (115 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (115 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case116 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (116 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (116 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case117 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (117 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (117 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case118 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (118 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (118 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case119 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (119 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (119 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case120 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (120 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (120 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case121 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (121 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (121 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case122 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (122 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (122 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case123 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (123 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (123 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case124 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (124 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (124 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case125 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (125 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (125 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case126 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (126 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (126 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case127 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (127 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (127 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case128 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (128 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (128 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case129 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (129 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (129 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case130 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (130 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (130 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case131 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (131 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (131 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case132 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (132 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (132 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case133 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (133 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (133 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case134 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (134 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (134 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case135 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (135 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (135 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case136 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (136 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (136 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case137 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (137 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (137 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case138 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (138 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (138 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case139 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (139 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (139 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case140 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (140 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (140 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case141 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (141 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (141 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case142 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (142 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (142 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen1_case143 : a6DoubleCoverBlockIndex (a6DoubleCoverGen1 (143 : Fin 144)) = a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex (143 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case0 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (0 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (0 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case1 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (1 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (1 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case2 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (2 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (2 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case3 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (3 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (3 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case4 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (4 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (4 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case5 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (5 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (5 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case6 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (6 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (6 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case7 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (7 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (7 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case8 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (8 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (8 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case9 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (9 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (9 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case10 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (10 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (10 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case11 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (11 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (11 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case12 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (12 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (12 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case13 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (13 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (13 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case14 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (14 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (14 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case15 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (15 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (15 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case16 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (16 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (16 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case17 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (17 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (17 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case18 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (18 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (18 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case19 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (19 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (19 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case20 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (20 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (20 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case21 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (21 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (21 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case22 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (22 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (22 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case23 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (23 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (23 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case24 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (24 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (24 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case25 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (25 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (25 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case26 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (26 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (26 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case27 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (27 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (27 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case28 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (28 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (28 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case29 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (29 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (29 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case30 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (30 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (30 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case31 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (31 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (31 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case32 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (32 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (32 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case33 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (33 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (33 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case34 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (34 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (34 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case35 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (35 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (35 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case36 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (36 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (36 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case37 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (37 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (37 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case38 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (38 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (38 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case39 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (39 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (39 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case40 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (40 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (40 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case41 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (41 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (41 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case42 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (42 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (42 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case43 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (43 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (43 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case44 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (44 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (44 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case45 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (45 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (45 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case46 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (46 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (46 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case47 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (47 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (47 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case48 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (48 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (48 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case49 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (49 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (49 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case50 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (50 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (50 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case51 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (51 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (51 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case52 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (52 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (52 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case53 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (53 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (53 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case54 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (54 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (54 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case55 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (55 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (55 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case56 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (56 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (56 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case57 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (57 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (57 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case58 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (58 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (58 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case59 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (59 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (59 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case60 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (60 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (60 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case61 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (61 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (61 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case62 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (62 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (62 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case63 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (63 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (63 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case64 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (64 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (64 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case65 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (65 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (65 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case66 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (66 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (66 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case67 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (67 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (67 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case68 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (68 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (68 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case69 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (69 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (69 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case70 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (70 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (70 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case71 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (71 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (71 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case72 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (72 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (72 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case73 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (73 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (73 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case74 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (74 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (74 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case75 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (75 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (75 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case76 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (76 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (76 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case77 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (77 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (77 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case78 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (78 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (78 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case79 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (79 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (79 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case80 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (80 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (80 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case81 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (81 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (81 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case82 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (82 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (82 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case83 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (83 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (83 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case84 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (84 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (84 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case85 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (85 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (85 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case86 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (86 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (86 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case87 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (87 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (87 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case88 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (88 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (88 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case89 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (89 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (89 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case90 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (90 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (90 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case91 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (91 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (91 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case92 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (92 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (92 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case93 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (93 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (93 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case94 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (94 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (94 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case95 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (95 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (95 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case96 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (96 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (96 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case97 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (97 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (97 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case98 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (98 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (98 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case99 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (99 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (99 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case100 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (100 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (100 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case101 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (101 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (101 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case102 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (102 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (102 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case103 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (103 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (103 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case104 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (104 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (104 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case105 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (105 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (105 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case106 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (106 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (106 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case107 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (107 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (107 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case108 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (108 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (108 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case109 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (109 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (109 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case110 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (110 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (110 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case111 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (111 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (111 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case112 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (112 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (112 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case113 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (113 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (113 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case114 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (114 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (114 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case115 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (115 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (115 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case116 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (116 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (116 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case117 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (117 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (117 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case118 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (118 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (118 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case119 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (119 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (119 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case120 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (120 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (120 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case121 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (121 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (121 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case122 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (122 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (122 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case123 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (123 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (123 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case124 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (124 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (124 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case125 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (125 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (125 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case126 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (126 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (126 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case127 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (127 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (127 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case128 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (128 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (128 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case129 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (129 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (129 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case130 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (130 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (130 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case131 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (131 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (131 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case132 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (132 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (132 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case133 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (133 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (133 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case134 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (134 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (134 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case135 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (135 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (135 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case136 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (136 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (136 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case137 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (137 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (137 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case138 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (138 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (138 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case139 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (139 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (139 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case140 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (140 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (140 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case141 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (141 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (141 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case142 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (142 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (142 : Fin 144)) := by rfl
private theorem a6DoubleCoverBlockIndex_gen2_case143 : a6DoubleCoverBlockIndex (a6DoubleCoverGen2 (143 : Fin 144)) = a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex (143 : Fin 144)) := by rfl
public lemma a6DoubleCoverBlockIndex_gen1 (x : Fin 144) :
    a6DoubleCoverBlockIndex (a6DoubleCoverGen1 x) =
      a6DoubleCoverQuotientGen1 (a6DoubleCoverBlockIndex x) := by
  fin_cases x
  · exact a6DoubleCoverBlockIndex_gen1_case0
  · exact a6DoubleCoverBlockIndex_gen1_case1
  · exact a6DoubleCoverBlockIndex_gen1_case2
  · exact a6DoubleCoverBlockIndex_gen1_case3
  · exact a6DoubleCoverBlockIndex_gen1_case4
  · exact a6DoubleCoverBlockIndex_gen1_case5
  · exact a6DoubleCoverBlockIndex_gen1_case6
  · exact a6DoubleCoverBlockIndex_gen1_case7
  · exact a6DoubleCoverBlockIndex_gen1_case8
  · exact a6DoubleCoverBlockIndex_gen1_case9
  · exact a6DoubleCoverBlockIndex_gen1_case10
  · exact a6DoubleCoverBlockIndex_gen1_case11
  · exact a6DoubleCoverBlockIndex_gen1_case12
  · exact a6DoubleCoverBlockIndex_gen1_case13
  · exact a6DoubleCoverBlockIndex_gen1_case14
  · exact a6DoubleCoverBlockIndex_gen1_case15
  · exact a6DoubleCoverBlockIndex_gen1_case16
  · exact a6DoubleCoverBlockIndex_gen1_case17
  · exact a6DoubleCoverBlockIndex_gen1_case18
  · exact a6DoubleCoverBlockIndex_gen1_case19
  · exact a6DoubleCoverBlockIndex_gen1_case20
  · exact a6DoubleCoverBlockIndex_gen1_case21
  · exact a6DoubleCoverBlockIndex_gen1_case22
  · exact a6DoubleCoverBlockIndex_gen1_case23
  · exact a6DoubleCoverBlockIndex_gen1_case24
  · exact a6DoubleCoverBlockIndex_gen1_case25
  · exact a6DoubleCoverBlockIndex_gen1_case26
  · exact a6DoubleCoverBlockIndex_gen1_case27
  · exact a6DoubleCoverBlockIndex_gen1_case28
  · exact a6DoubleCoverBlockIndex_gen1_case29
  · exact a6DoubleCoverBlockIndex_gen1_case30
  · exact a6DoubleCoverBlockIndex_gen1_case31
  · exact a6DoubleCoverBlockIndex_gen1_case32
  · exact a6DoubleCoverBlockIndex_gen1_case33
  · exact a6DoubleCoverBlockIndex_gen1_case34
  · exact a6DoubleCoverBlockIndex_gen1_case35
  · exact a6DoubleCoverBlockIndex_gen1_case36
  · exact a6DoubleCoverBlockIndex_gen1_case37
  · exact a6DoubleCoverBlockIndex_gen1_case38
  · exact a6DoubleCoverBlockIndex_gen1_case39
  · exact a6DoubleCoverBlockIndex_gen1_case40
  · exact a6DoubleCoverBlockIndex_gen1_case41
  · exact a6DoubleCoverBlockIndex_gen1_case42
  · exact a6DoubleCoverBlockIndex_gen1_case43
  · exact a6DoubleCoverBlockIndex_gen1_case44
  · exact a6DoubleCoverBlockIndex_gen1_case45
  · exact a6DoubleCoverBlockIndex_gen1_case46
  · exact a6DoubleCoverBlockIndex_gen1_case47
  · exact a6DoubleCoverBlockIndex_gen1_case48
  · exact a6DoubleCoverBlockIndex_gen1_case49
  · exact a6DoubleCoverBlockIndex_gen1_case50
  · exact a6DoubleCoverBlockIndex_gen1_case51
  · exact a6DoubleCoverBlockIndex_gen1_case52
  · exact a6DoubleCoverBlockIndex_gen1_case53
  · exact a6DoubleCoverBlockIndex_gen1_case54
  · exact a6DoubleCoverBlockIndex_gen1_case55
  · exact a6DoubleCoverBlockIndex_gen1_case56
  · exact a6DoubleCoverBlockIndex_gen1_case57
  · exact a6DoubleCoverBlockIndex_gen1_case58
  · exact a6DoubleCoverBlockIndex_gen1_case59
  · exact a6DoubleCoverBlockIndex_gen1_case60
  · exact a6DoubleCoverBlockIndex_gen1_case61
  · exact a6DoubleCoverBlockIndex_gen1_case62
  · exact a6DoubleCoverBlockIndex_gen1_case63
  · exact a6DoubleCoverBlockIndex_gen1_case64
  · exact a6DoubleCoverBlockIndex_gen1_case65
  · exact a6DoubleCoverBlockIndex_gen1_case66
  · exact a6DoubleCoverBlockIndex_gen1_case67
  · exact a6DoubleCoverBlockIndex_gen1_case68
  · exact a6DoubleCoverBlockIndex_gen1_case69
  · exact a6DoubleCoverBlockIndex_gen1_case70
  · exact a6DoubleCoverBlockIndex_gen1_case71
  · exact a6DoubleCoverBlockIndex_gen1_case72
  · exact a6DoubleCoverBlockIndex_gen1_case73
  · exact a6DoubleCoverBlockIndex_gen1_case74
  · exact a6DoubleCoverBlockIndex_gen1_case75
  · exact a6DoubleCoverBlockIndex_gen1_case76
  · exact a6DoubleCoverBlockIndex_gen1_case77
  · exact a6DoubleCoverBlockIndex_gen1_case78
  · exact a6DoubleCoverBlockIndex_gen1_case79
  · exact a6DoubleCoverBlockIndex_gen1_case80
  · exact a6DoubleCoverBlockIndex_gen1_case81
  · exact a6DoubleCoverBlockIndex_gen1_case82
  · exact a6DoubleCoverBlockIndex_gen1_case83
  · exact a6DoubleCoverBlockIndex_gen1_case84
  · exact a6DoubleCoverBlockIndex_gen1_case85
  · exact a6DoubleCoverBlockIndex_gen1_case86
  · exact a6DoubleCoverBlockIndex_gen1_case87
  · exact a6DoubleCoverBlockIndex_gen1_case88
  · exact a6DoubleCoverBlockIndex_gen1_case89
  · exact a6DoubleCoverBlockIndex_gen1_case90
  · exact a6DoubleCoverBlockIndex_gen1_case91
  · exact a6DoubleCoverBlockIndex_gen1_case92
  · exact a6DoubleCoverBlockIndex_gen1_case93
  · exact a6DoubleCoverBlockIndex_gen1_case94
  · exact a6DoubleCoverBlockIndex_gen1_case95
  · exact a6DoubleCoverBlockIndex_gen1_case96
  · exact a6DoubleCoverBlockIndex_gen1_case97
  · exact a6DoubleCoverBlockIndex_gen1_case98
  · exact a6DoubleCoverBlockIndex_gen1_case99
  · exact a6DoubleCoverBlockIndex_gen1_case100
  · exact a6DoubleCoverBlockIndex_gen1_case101
  · exact a6DoubleCoverBlockIndex_gen1_case102
  · exact a6DoubleCoverBlockIndex_gen1_case103
  · exact a6DoubleCoverBlockIndex_gen1_case104
  · exact a6DoubleCoverBlockIndex_gen1_case105
  · exact a6DoubleCoverBlockIndex_gen1_case106
  · exact a6DoubleCoverBlockIndex_gen1_case107
  · exact a6DoubleCoverBlockIndex_gen1_case108
  · exact a6DoubleCoverBlockIndex_gen1_case109
  · exact a6DoubleCoverBlockIndex_gen1_case110
  · exact a6DoubleCoverBlockIndex_gen1_case111
  · exact a6DoubleCoverBlockIndex_gen1_case112
  · exact a6DoubleCoverBlockIndex_gen1_case113
  · exact a6DoubleCoverBlockIndex_gen1_case114
  · exact a6DoubleCoverBlockIndex_gen1_case115
  · exact a6DoubleCoverBlockIndex_gen1_case116
  · exact a6DoubleCoverBlockIndex_gen1_case117
  · exact a6DoubleCoverBlockIndex_gen1_case118
  · exact a6DoubleCoverBlockIndex_gen1_case119
  · exact a6DoubleCoverBlockIndex_gen1_case120
  · exact a6DoubleCoverBlockIndex_gen1_case121
  · exact a6DoubleCoverBlockIndex_gen1_case122
  · exact a6DoubleCoverBlockIndex_gen1_case123
  · exact a6DoubleCoverBlockIndex_gen1_case124
  · exact a6DoubleCoverBlockIndex_gen1_case125
  · exact a6DoubleCoverBlockIndex_gen1_case126
  · exact a6DoubleCoverBlockIndex_gen1_case127
  · exact a6DoubleCoverBlockIndex_gen1_case128
  · exact a6DoubleCoverBlockIndex_gen1_case129
  · exact a6DoubleCoverBlockIndex_gen1_case130
  · exact a6DoubleCoverBlockIndex_gen1_case131
  · exact a6DoubleCoverBlockIndex_gen1_case132
  · exact a6DoubleCoverBlockIndex_gen1_case133
  · exact a6DoubleCoverBlockIndex_gen1_case134
  · exact a6DoubleCoverBlockIndex_gen1_case135
  · exact a6DoubleCoverBlockIndex_gen1_case136
  · exact a6DoubleCoverBlockIndex_gen1_case137
  · exact a6DoubleCoverBlockIndex_gen1_case138
  · exact a6DoubleCoverBlockIndex_gen1_case139
  · exact a6DoubleCoverBlockIndex_gen1_case140
  · exact a6DoubleCoverBlockIndex_gen1_case141
  · exact a6DoubleCoverBlockIndex_gen1_case142
  · exact a6DoubleCoverBlockIndex_gen1_case143
public lemma a6DoubleCoverBlockIndex_gen2 (x : Fin 144) :
    a6DoubleCoverBlockIndex (a6DoubleCoverGen2 x) =
      a6DoubleCoverQuotientGen2 (a6DoubleCoverBlockIndex x) := by
  fin_cases x
  · exact a6DoubleCoverBlockIndex_gen2_case0
  · exact a6DoubleCoverBlockIndex_gen2_case1
  · exact a6DoubleCoverBlockIndex_gen2_case2
  · exact a6DoubleCoverBlockIndex_gen2_case3
  · exact a6DoubleCoverBlockIndex_gen2_case4
  · exact a6DoubleCoverBlockIndex_gen2_case5
  · exact a6DoubleCoverBlockIndex_gen2_case6
  · exact a6DoubleCoverBlockIndex_gen2_case7
  · exact a6DoubleCoverBlockIndex_gen2_case8
  · exact a6DoubleCoverBlockIndex_gen2_case9
  · exact a6DoubleCoverBlockIndex_gen2_case10
  · exact a6DoubleCoverBlockIndex_gen2_case11
  · exact a6DoubleCoverBlockIndex_gen2_case12
  · exact a6DoubleCoverBlockIndex_gen2_case13
  · exact a6DoubleCoverBlockIndex_gen2_case14
  · exact a6DoubleCoverBlockIndex_gen2_case15
  · exact a6DoubleCoverBlockIndex_gen2_case16
  · exact a6DoubleCoverBlockIndex_gen2_case17
  · exact a6DoubleCoverBlockIndex_gen2_case18
  · exact a6DoubleCoverBlockIndex_gen2_case19
  · exact a6DoubleCoverBlockIndex_gen2_case20
  · exact a6DoubleCoverBlockIndex_gen2_case21
  · exact a6DoubleCoverBlockIndex_gen2_case22
  · exact a6DoubleCoverBlockIndex_gen2_case23
  · exact a6DoubleCoverBlockIndex_gen2_case24
  · exact a6DoubleCoverBlockIndex_gen2_case25
  · exact a6DoubleCoverBlockIndex_gen2_case26
  · exact a6DoubleCoverBlockIndex_gen2_case27
  · exact a6DoubleCoverBlockIndex_gen2_case28
  · exact a6DoubleCoverBlockIndex_gen2_case29
  · exact a6DoubleCoverBlockIndex_gen2_case30
  · exact a6DoubleCoverBlockIndex_gen2_case31
  · exact a6DoubleCoverBlockIndex_gen2_case32
  · exact a6DoubleCoverBlockIndex_gen2_case33
  · exact a6DoubleCoverBlockIndex_gen2_case34
  · exact a6DoubleCoverBlockIndex_gen2_case35
  · exact a6DoubleCoverBlockIndex_gen2_case36
  · exact a6DoubleCoverBlockIndex_gen2_case37
  · exact a6DoubleCoverBlockIndex_gen2_case38
  · exact a6DoubleCoverBlockIndex_gen2_case39
  · exact a6DoubleCoverBlockIndex_gen2_case40
  · exact a6DoubleCoverBlockIndex_gen2_case41
  · exact a6DoubleCoverBlockIndex_gen2_case42
  · exact a6DoubleCoverBlockIndex_gen2_case43
  · exact a6DoubleCoverBlockIndex_gen2_case44
  · exact a6DoubleCoverBlockIndex_gen2_case45
  · exact a6DoubleCoverBlockIndex_gen2_case46
  · exact a6DoubleCoverBlockIndex_gen2_case47
  · exact a6DoubleCoverBlockIndex_gen2_case48
  · exact a6DoubleCoverBlockIndex_gen2_case49
  · exact a6DoubleCoverBlockIndex_gen2_case50
  · exact a6DoubleCoverBlockIndex_gen2_case51
  · exact a6DoubleCoverBlockIndex_gen2_case52
  · exact a6DoubleCoverBlockIndex_gen2_case53
  · exact a6DoubleCoverBlockIndex_gen2_case54
  · exact a6DoubleCoverBlockIndex_gen2_case55
  · exact a6DoubleCoverBlockIndex_gen2_case56
  · exact a6DoubleCoverBlockIndex_gen2_case57
  · exact a6DoubleCoverBlockIndex_gen2_case58
  · exact a6DoubleCoverBlockIndex_gen2_case59
  · exact a6DoubleCoverBlockIndex_gen2_case60
  · exact a6DoubleCoverBlockIndex_gen2_case61
  · exact a6DoubleCoverBlockIndex_gen2_case62
  · exact a6DoubleCoverBlockIndex_gen2_case63
  · exact a6DoubleCoverBlockIndex_gen2_case64
  · exact a6DoubleCoverBlockIndex_gen2_case65
  · exact a6DoubleCoverBlockIndex_gen2_case66
  · exact a6DoubleCoverBlockIndex_gen2_case67
  · exact a6DoubleCoverBlockIndex_gen2_case68
  · exact a6DoubleCoverBlockIndex_gen2_case69
  · exact a6DoubleCoverBlockIndex_gen2_case70
  · exact a6DoubleCoverBlockIndex_gen2_case71
  · exact a6DoubleCoverBlockIndex_gen2_case72
  · exact a6DoubleCoverBlockIndex_gen2_case73
  · exact a6DoubleCoverBlockIndex_gen2_case74
  · exact a6DoubleCoverBlockIndex_gen2_case75
  · exact a6DoubleCoverBlockIndex_gen2_case76
  · exact a6DoubleCoverBlockIndex_gen2_case77
  · exact a6DoubleCoverBlockIndex_gen2_case78
  · exact a6DoubleCoverBlockIndex_gen2_case79
  · exact a6DoubleCoverBlockIndex_gen2_case80
  · exact a6DoubleCoverBlockIndex_gen2_case81
  · exact a6DoubleCoverBlockIndex_gen2_case82
  · exact a6DoubleCoverBlockIndex_gen2_case83
  · exact a6DoubleCoverBlockIndex_gen2_case84
  · exact a6DoubleCoverBlockIndex_gen2_case85
  · exact a6DoubleCoverBlockIndex_gen2_case86
  · exact a6DoubleCoverBlockIndex_gen2_case87
  · exact a6DoubleCoverBlockIndex_gen2_case88
  · exact a6DoubleCoverBlockIndex_gen2_case89
  · exact a6DoubleCoverBlockIndex_gen2_case90
  · exact a6DoubleCoverBlockIndex_gen2_case91
  · exact a6DoubleCoverBlockIndex_gen2_case92
  · exact a6DoubleCoverBlockIndex_gen2_case93
  · exact a6DoubleCoverBlockIndex_gen2_case94
  · exact a6DoubleCoverBlockIndex_gen2_case95
  · exact a6DoubleCoverBlockIndex_gen2_case96
  · exact a6DoubleCoverBlockIndex_gen2_case97
  · exact a6DoubleCoverBlockIndex_gen2_case98
  · exact a6DoubleCoverBlockIndex_gen2_case99
  · exact a6DoubleCoverBlockIndex_gen2_case100
  · exact a6DoubleCoverBlockIndex_gen2_case101
  · exact a6DoubleCoverBlockIndex_gen2_case102
  · exact a6DoubleCoverBlockIndex_gen2_case103
  · exact a6DoubleCoverBlockIndex_gen2_case104
  · exact a6DoubleCoverBlockIndex_gen2_case105
  · exact a6DoubleCoverBlockIndex_gen2_case106
  · exact a6DoubleCoverBlockIndex_gen2_case107
  · exact a6DoubleCoverBlockIndex_gen2_case108
  · exact a6DoubleCoverBlockIndex_gen2_case109
  · exact a6DoubleCoverBlockIndex_gen2_case110
  · exact a6DoubleCoverBlockIndex_gen2_case111
  · exact a6DoubleCoverBlockIndex_gen2_case112
  · exact a6DoubleCoverBlockIndex_gen2_case113
  · exact a6DoubleCoverBlockIndex_gen2_case114
  · exact a6DoubleCoverBlockIndex_gen2_case115
  · exact a6DoubleCoverBlockIndex_gen2_case116
  · exact a6DoubleCoverBlockIndex_gen2_case117
  · exact a6DoubleCoverBlockIndex_gen2_case118
  · exact a6DoubleCoverBlockIndex_gen2_case119
  · exact a6DoubleCoverBlockIndex_gen2_case120
  · exact a6DoubleCoverBlockIndex_gen2_case121
  · exact a6DoubleCoverBlockIndex_gen2_case122
  · exact a6DoubleCoverBlockIndex_gen2_case123
  · exact a6DoubleCoverBlockIndex_gen2_case124
  · exact a6DoubleCoverBlockIndex_gen2_case125
  · exact a6DoubleCoverBlockIndex_gen2_case126
  · exact a6DoubleCoverBlockIndex_gen2_case127
  · exact a6DoubleCoverBlockIndex_gen2_case128
  · exact a6DoubleCoverBlockIndex_gen2_case129
  · exact a6DoubleCoverBlockIndex_gen2_case130
  · exact a6DoubleCoverBlockIndex_gen2_case131
  · exact a6DoubleCoverBlockIndex_gen2_case132
  · exact a6DoubleCoverBlockIndex_gen2_case133
  · exact a6DoubleCoverBlockIndex_gen2_case134
  · exact a6DoubleCoverBlockIndex_gen2_case135
  · exact a6DoubleCoverBlockIndex_gen2_case136
  · exact a6DoubleCoverBlockIndex_gen2_case137
  · exact a6DoubleCoverBlockIndex_gen2_case138
  · exact a6DoubleCoverBlockIndex_gen2_case139
  · exact a6DoubleCoverBlockIndex_gen2_case140
  · exact a6DoubleCoverBlockIndex_gen2_case141
  · exact a6DoubleCoverBlockIndex_gen2_case142
  · exact a6DoubleCoverBlockIndex_gen2_case143

public lemma a6DoubleCoverBlockIndex_surjective : Function.Surjective a6DoubleCoverBlockIndex := by
  intro i
  fin_cases i
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨7, by decide⟩
  · exact ⟨13, by decide⟩

public lemma a6DoubleCoverSubgroup_le_fiber : a6DoubleCoverPermutationSubgroup ≤ FiberAction.subgroup a6DoubleCoverBlockIndex := by
  rw [a6DoubleCoverPermutationSubgroup, Subgroup.closure_le]
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact ⟨a6DoubleCoverQuotientGen1, a6DoubleCoverBlockIndex_gen1⟩
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨a6DoubleCoverQuotientGen2, a6DoubleCoverBlockIndex_gen2⟩

@[expose] public noncomputable def a6DoubleCoverToFiberHom : a6DoubleCoverPermutationSubgroup →*
    FiberAction.subgroup a6DoubleCoverBlockIndex :=
  Subgroup.inclusion a6DoubleCoverSubgroup_le_fiber

@[expose] public noncomputable def a6DoubleCoverBlockPermHom : a6DoubleCoverPermutationSubgroup →* Equiv.Perm (Fin 6) :=
  (FiberAction.quotientHom a6DoubleCoverBlockIndex a6DoubleCoverBlockIndex_surjective).comp a6DoubleCoverToFiberHom

@[expose] public def a6DoubleCoverGen1Sub : a6DoubleCoverPermutationSubgroup :=
  ⟨a6DoubleCoverGen1, Subgroup.subset_closure (Set.mem_insert _ _)⟩
@[expose] public def a6DoubleCoverGen2Sub : a6DoubleCoverPermutationSubgroup :=
  ⟨a6DoubleCoverGen2, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

public lemma a6DoubleCoverBlockPermHom_gen1 : a6DoubleCoverBlockPermHom a6DoubleCoverGen1Sub = a6DoubleCoverQuotientGen1 := by
  apply FiberAction.quotient_unique a6DoubleCoverBlockIndex a6DoubleCoverBlockIndex_surjective
  · exact FiberAction.quotientPerm_spec a6DoubleCoverBlockIndex (a6DoubleCoverToFiberHom a6DoubleCoverGen1Sub)
  · exact a6DoubleCoverBlockIndex_gen1
public lemma a6DoubleCoverBlockPermHom_gen2 : a6DoubleCoverBlockPermHom a6DoubleCoverGen2Sub = a6DoubleCoverQuotientGen2 := by
  apply FiberAction.quotient_unique a6DoubleCoverBlockIndex a6DoubleCoverBlockIndex_surjective
  · exact FiberAction.quotientPerm_spec a6DoubleCoverBlockIndex (a6DoubleCoverToFiberHom a6DoubleCoverGen2Sub)
  · exact a6DoubleCoverBlockIndex_gen2

public lemma a6DoubleCoverBlockPermHom_mem_alternating (g : a6DoubleCoverPermutationSubgroup) :
    a6DoubleCoverBlockPermHom g ∈ alternatingGroup (Fin 6) := by
  rcases g with ⟨g, hg⟩
  change Equiv.Perm.sign (a6DoubleCoverBlockPermHom ⟨g, hg⟩) = 1
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · change Equiv.Perm.sign
          (a6DoubleCoverBlockPermHom a6DoubleCoverGen1Sub) = 1
        rw [a6DoubleCoverBlockPermHom_gen1]
        all_goals decide
      · rw [Set.mem_singleton_iff] at hg
        subst g
        change Equiv.Perm.sign
          (a6DoubleCoverBlockPermHom a6DoubleCoverGen2Sub) = 1
        rw [a6DoubleCoverBlockPermHom_gen2]
        all_goals decide
  | one =>
      change Equiv.Perm.sign (a6DoubleCoverBlockPermHom 1) = 1
      rw [map_one, Equiv.Perm.sign_one]
  | mul x y hx hy ihx ihy =>
      change Equiv.Perm.sign (a6DoubleCoverBlockPermHom (⟨x, hx⟩ * ⟨y, hy⟩)) = 1
      rw [map_mul, Equiv.Perm.sign_mul, ihx, ihy, one_mul]
  | inv x hx ih =>
      change Equiv.Perm.sign (a6DoubleCoverBlockPermHom (⟨x, hx⟩⁻¹)) = 1
      rw [map_inv, Equiv.Perm.sign_inv, ih]

@[expose] public noncomputable def a6DoubleCoverBlockCoverHom : a6DoubleCoverPermutationSubgroup →*
    alternatingGroup (Fin 6) :=
  a6DoubleCoverBlockPermHom.codRestrict (alternatingGroup (Fin 6)) a6DoubleCoverBlockPermHom_mem_alternating

public lemma a6DoubleCoverBlockCoverHom_gen1 : a6DoubleCoverBlockCoverHom a6DoubleCoverGen1Sub = ⟨a6DoubleCoverQuotientGen1, by change Equiv.Perm.sign a6DoubleCoverQuotientGen1 = 1; decide⟩ := by
  apply Subtype.ext
  exact a6DoubleCoverBlockPermHom_gen1
public lemma a6DoubleCoverBlockCoverHom_gen2 : a6DoubleCoverBlockCoverHom a6DoubleCoverGen2Sub = ⟨a6DoubleCoverQuotientGen2, by change Equiv.Perm.sign a6DoubleCoverQuotientGen2 = 1; decide⟩ := by
  apply Subtype.ext
  exact a6DoubleCoverBlockPermHom_gen2

public lemma a6AlternatingSuzukiGenerator_mem_range (i : Fin 4) :
    alternatingSuzukiGenerator 1 i ∈ a6DoubleCoverBlockCoverHom.range := by
  fin_cases i
  · refine ⟨a6DoubleCoverGen2Sub, ?_⟩
    rw [a6DoubleCoverBlockCoverHom_gen2]
    apply Subtype.ext
    all_goals decide
  · refine ⟨a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub, ?_⟩
    simp only [map_mul, map_inv, a6DoubleCoverBlockCoverHom_gen1, a6DoubleCoverBlockCoverHom_gen2]
    apply Subtype.ext
    all_goals decide
  · refine ⟨a6DoubleCoverGen1Sub ^ 2 * a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub, ?_⟩
    simp only [map_mul, map_inv, map_pow, a6DoubleCoverBlockCoverHom_gen1, a6DoubleCoverBlockCoverHom_gen2]
    apply Subtype.ext
    all_goals decide
  · refine ⟨a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub ^ 2, ?_⟩
    simp only [map_mul, map_inv, map_pow, a6DoubleCoverBlockCoverHom_gen1, a6DoubleCoverBlockCoverHom_gen2]
    apply Subtype.ext
    all_goals decide
public lemma a6DoubleCoverBlockCoverHom_surjective : Function.Surjective a6DoubleCoverBlockCoverHom := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← alternatingSuzukiGenerator_closure_eq_top 1]
  apply (Subgroup.closure_le a6DoubleCoverBlockCoverHom.range).2
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact a6AlternatingSuzukiGenerator_mem_range i

public theorem a6DoubleCoverBlockCoverHom_kernel_card :
    Nat.card a6DoubleCoverBlockCoverHom.ker = 2 := by
  have h := card_comap_mul a6DoubleCoverBlockCoverHom
    a6DoubleCoverBlockCoverHom_surjective
    (⊤ : Subgroup (alternatingGroup (Fin 6)))
  have hcod : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num
  rw [show (⊤ : Subgroup (alternatingGroup (Fin 6))).comap
      a6DoubleCoverBlockCoverHom = ⊤ by rfl,
    Nat.card_congr Subgroup.topEquiv.toEquiv,
    a6DoubleCoverPermutationSubgroup_card,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hcod] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 360) h.symm

end GLS3.Chapter5
/- END Theory.A6DoubleCoverBlockAction -/

/- BEGIN Theory.A6DoubleCoverNormalForm -/
namespace GLS3.Chapter5

private theorem __ch5_A6DoubleCoverNormalForm_a6ChainRepPoint0 (r : Fin 144) :
    a6ChainRep0 r 0 = r := by
  fin_cases r <;> decide +revert +kernel

public theorem a6ChainRepPoint1 (r : Fin 5) :
    a6ChainRep1 r 1 = a6ChainPoint1 r := by
  decide +revert +kernel

public theorem a6ChainPoint1_injective : Function.Injective a6ChainPoint1 := by
  decide +revert +kernel

end GLS3.Chapter5

namespace GLS3.Chapter5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem __ch5_A6DoubleCoverNormalForm_a6EvalWordGen0_mem (w : List (Fin 4)) :
    evalWord a6ChainGen0 w ∈ a6DoubleCoverPermutationSubgroup := by
  induction w with
  | nil => exact a6DoubleCoverPermutationSubgroup.one_mem
  | cons i w ih =>
      apply a6DoubleCoverPermutationSubgroup.mul_mem _ ih
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact a6DoubleCoverPermutationSubgroup.inv_mem
          (Subgroup.subset_closure (Set.mem_insert _ _))
      · exact Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact a6DoubleCoverPermutationSubgroup.inv_mem
          (Subgroup.subset_closure
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem __ch5_A6DoubleCoverNormalForm_a6EvalWordGen1_mem (w : List (Fin 2)) :
    evalWord a6ChainGen1 w ∈ a6DoubleCoverPermutationSubgroup := by
  induction w with
  | nil => exact a6DoubleCoverPermutationSubgroup.one_mem
  | cons i w ih =>
      apply a6DoubleCoverPermutationSubgroup.mul_mem _ ih
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact a6DoubleCoverPermutationSubgroup.inv_mem
          (Subgroup.subset_closure (Set.mem_insert _ _))

public theorem a6ChainRep0_mem (r : Fin 144) :
    a6ChainRep0 r ∈ a6DoubleCoverPermutationSubgroup :=
  __ch5_A6DoubleCoverNormalForm_a6EvalWordGen0_mem (a6ChainRepWord0 r)

public theorem a6ChainRep1_mem (s : Fin 5) :
    a6ChainRep1 s ∈ a6DoubleCoverPermutationSubgroup :=
  __ch5_A6DoubleCoverNormalForm_a6EvalWordGen1_mem (a6ChainRepWord1 s)

@[expose] public def a6DoubleCoverNormalForm (x : Fin 144 × Fin 5) :
    a6DoubleCoverPermutationSubgroup :=
  ⟨a6ChainRep0 x.1 * a6ChainRep1 x.2,
    a6DoubleCoverPermutationSubgroup.mul_mem
      (a6ChainRep0_mem x.1) (a6ChainRep1_mem x.2)⟩

private theorem __ch5_A6DoubleCoverNormalForm_a6ChainRep1_point0 (s : Fin 5) : a6ChainRep1 s 0 = 0 := by
  fin_cases s <;> decide +revert +kernel

public theorem a6DoubleCoverNormalForm_injective :
    Function.Injective a6DoubleCoverNormalForm := by
  intro x y hxy
  rcases x with ⟨r, s⟩
  rcases y with ⟨t, u⟩
  have hperm : a6ChainRep0 r * a6ChainRep1 s =
      a6ChainRep0 t * a6ChainRep1 u := Subtype.ext_iff.mp hxy
  have hr : r = t := by
    have hpoint := congrArg (fun g : Perm144 => g 0) hperm
    simpa [Equiv.Perm.mul_apply, __ch5_A6DoubleCoverNormalForm_a6ChainRep1_point0,
      __ch5_A6DoubleCoverNormalForm_a6ChainRepPoint0] using hpoint
  subst t
  have hrep : a6ChainRep1 s = a6ChainRep1 u := mul_left_cancel hperm
  have hpoint := congrArg (fun g : Perm144 => g 1) hrep
  have hsu : a6ChainPoint1 s = a6ChainPoint1 u := by
    simpa [a6ChainRepPoint1] using hpoint
  have := a6ChainPoint1_injective hsu
  subst u
  rfl

public theorem a6DoubleCoverNormalForm_surjective :
    Function.Surjective a6DoubleCoverNormalForm := by
  apply ((Nat.bijective_iff_injective_and_card a6DoubleCoverNormalForm).2
    ⟨a6DoubleCoverNormalForm_injective, ?_⟩).2
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin,
    a6DoubleCoverPermutationSubgroup_card]

@[expose] public noncomputable def a6DoubleCoverNormalFormEquiv :
    (Fin 144 × Fin 5) ≃ a6DoubleCoverPermutationSubgroup :=
  Equiv.ofBijective a6DoubleCoverNormalForm
    ⟨a6DoubleCoverNormalForm_injective, a6DoubleCoverNormalForm_surjective⟩

public theorem a6DoubleCoverNormalFormEquiv_apply (x : Fin 144 × Fin 5) :
    a6DoubleCoverNormalFormEquiv x = a6DoubleCoverNormalForm x := rfl

end GLS3.Chapter5
/- END Theory.A6DoubleCoverNormalForm -/

/- BEGIN Theory.A6DoubleCoverExceptionalAut -/
namespace GLS3.Chapter5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem a6ExceptionalConjugator_conj_gen1 :
    a6ExceptionalConjugator⁻¹ * a6DoubleCoverGen1 * a6ExceptionalConjugator =
      a6DoubleCoverGen1⁻¹ * a6DoubleCoverGen2⁻¹ * a6DoubleCoverGen1 *
        a6DoubleCoverGen2 * a6DoubleCoverGen1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

public theorem a6ExceptionalConjugator_conj_gen2 :
    a6ExceptionalConjugator⁻¹ * a6DoubleCoverGen2 * a6ExceptionalConjugator =
      a6DoubleCoverGen1 * a6DoubleCoverGen2 * a6DoubleCoverGen1 *
        a6DoubleCoverGen2⁻¹ * a6DoubleCoverGen1⁻¹ * a6DoubleCoverGen2⁻¹ := by
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

private theorem __ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv :
    a6ExceptionalConjugator⁻¹ = a6ExceptionalConjugator := by
  apply inv_eq_of_mul_eq_one_left
  simpa [pow_two] using a6ExceptionalConjugator_sq

private theorem __ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_conj_mem
    (g : Perm144) (hg : g ∈ a6DoubleCoverPermutationSubgroup) :
    a6ExceptionalConjugator⁻¹ * g * a6ExceptionalConjugator ∈
      a6DoubleCoverPermutationSubgroup := by
  let H := a6DoubleCoverPermutationSubgroup
  have h1 : a6DoubleCoverGen1 ∈ H :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : a6DoubleCoverGen2 ∈ H :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · rw [a6ExceptionalConjugator_conj_gen1]
        exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem h1)
          (H.inv_mem h2)) h1) h2) h1
      · rw [Set.mem_singleton_iff] at hg
        subst g
        rw [a6ExceptionalConjugator_conj_gen2]
        exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem h1 h2) h1)
          (H.inv_mem h2)) (H.inv_mem h1)) (H.inv_mem h2)
  | one => simp
  | mul g h hg hh ig ih =>
      rw [show a6ExceptionalConjugator⁻¹ * (g * h) * a6ExceptionalConjugator =
          (a6ExceptionalConjugator⁻¹ * g * a6ExceptionalConjugator) *
            (a6ExceptionalConjugator⁻¹ * h * a6ExceptionalConjugator) by
        rw [__ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv]
        calc
          a6ExceptionalConjugator * (g * h) * a6ExceptionalConjugator =
              a6ExceptionalConjugator * g * h * a6ExceptionalConjugator := by group
          _ = a6ExceptionalConjugator * g * (a6ExceptionalConjugator *
                a6ExceptionalConjugator) * h * a6ExceptionalConjugator := by
              rw [show a6ExceptionalConjugator * a6ExceptionalConjugator = 1 by
                simpa [pow_two] using a6ExceptionalConjugator_sq]
              group
          _ = (a6ExceptionalConjugator * g * a6ExceptionalConjugator) *
                (a6ExceptionalConjugator * h * a6ExceptionalConjugator) := by group]
      exact H.mul_mem ig ih
  | inv g hg ih =>
      rw [show a6ExceptionalConjugator⁻¹ * g⁻¹ * a6ExceptionalConjugator =
          (a6ExceptionalConjugator⁻¹ * g * a6ExceptionalConjugator)⁻¹ by group]
      exact H.inv_mem ih

public theorem a6ExceptionalConjugator_mem_normalizer :
    a6ExceptionalConjugator ∈
      Subgroup.normalizer (a6DoubleCoverPermutationSubgroup : Set Perm144) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rw [__ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv]
    exact __ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_conj_mem g
  · intro hg
    have h := __ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_conj_mem
      (a6ExceptionalConjugator⁻¹ * g * a6ExceptionalConjugator) hg
    rw [__ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv] at h
    have heq : a6ExceptionalConjugator * (a6ExceptionalConjugator * g *
        a6ExceptionalConjugator) * a6ExceptionalConjugator = g := by
      calc
        a6ExceptionalConjugator * (a6ExceptionalConjugator * g *
            a6ExceptionalConjugator) * a6ExceptionalConjugator =
            (a6ExceptionalConjugator * a6ExceptionalConjugator) * g *
              (a6ExceptionalConjugator * a6ExceptionalConjugator) := by group
        _ = g := by
          rw [show a6ExceptionalConjugator * a6ExceptionalConjugator = 1 by
            simpa [pow_two] using a6ExceptionalConjugator_sq]
          simp
    rw [heq] at h
    exact h

public noncomputable def a6ExceptionalConjugatorLiftAut :
    MulAut a6DoubleCoverPermutationSubgroup := by
  let f : a6DoubleCoverPermutationSubgroup →* a6DoubleCoverPermutationSubgroup :=
    { toFun := fun g => ⟨a6ExceptionalConjugator⁻¹ * (g : Perm144) *
        a6ExceptionalConjugator, __ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_conj_mem g g.property⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        change a6ExceptionalConjugator⁻¹ * ((g : Perm144) * (h : Perm144)) *
            a6ExceptionalConjugator =
          (a6ExceptionalConjugator⁻¹ * (g : Perm144) * a6ExceptionalConjugator) *
            (a6ExceptionalConjugator⁻¹ * (h : Perm144) * a6ExceptionalConjugator)
        rw [__ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv]
        calc
          a6ExceptionalConjugator * ((g : Perm144) * h) * a6ExceptionalConjugator =
              a6ExceptionalConjugator * g * h * a6ExceptionalConjugator := by group
          _ = a6ExceptionalConjugator * g * (a6ExceptionalConjugator *
                a6ExceptionalConjugator) * h * a6ExceptionalConjugator := by
              rw [show a6ExceptionalConjugator * a6ExceptionalConjugator = 1 by
                simpa [pow_two] using a6ExceptionalConjugator_sq]
              group
          _ = (a6ExceptionalConjugator * g * a6ExceptionalConjugator) *
                (a6ExceptionalConjugator * h * a6ExceptionalConjugator) := by group }
  have hf_involutive : Function.Involutive f := by
    intro h
    apply Subtype.ext
    change a6ExceptionalConjugator⁻¹ *
        (a6ExceptionalConjugator⁻¹ * (h : Perm144) * a6ExceptionalConjugator) *
        a6ExceptionalConjugator = h
    rw [__ch5_A6DoubleCoverExceptionalAut_a6ExceptionalConjugator_inv]
    calc
      a6ExceptionalConjugator * (a6ExceptionalConjugator * (h : Perm144) *
          a6ExceptionalConjugator) * a6ExceptionalConjugator =
          (a6ExceptionalConjugator * a6ExceptionalConjugator) * h *
            (a6ExceptionalConjugator * a6ExceptionalConjugator) := by group
      _ = h := by
        rw [show a6ExceptionalConjugator * a6ExceptionalConjugator = 1 by
          simpa [pow_two] using a6ExceptionalConjugator_sq]
        simp
  exact MulEquiv.ofBijective f ⟨hf_involutive.injective, hf_involutive.surjective⟩

public theorem a6ExceptionalConjugatorLiftAut_apply (g : a6DoubleCoverPermutationSubgroup) :
    (a6ExceptionalConjugatorLiftAut g : Perm144) =
      a6ExceptionalConjugator⁻¹ * (g : Perm144) * a6ExceptionalConjugator := by
  rfl

end GLS3.Chapter5
/- END Theory.A6DoubleCoverExceptionalAut -/

/- BEGIN Theory.A6DoubleCoverFixedData -/
namespace GLS3.Chapter5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

@[reducible, expose] public def a6ExceptionalFixedNormalIndices :
    Finset (Fin 144 × Fin 5) :=
  {(0,0),(20,3),(49,1),(54,0),(85,2),(94,4),(96,1),(102,1),(125,0),(133,2)}

public theorem a6ExceptionalFixedNormalIndices_card :
    a6ExceptionalFixedNormalIndices.card = 10 := by decide

end GLS3.Chapter5
/- END Theory.A6DoubleCoverFixedData -/

/- BEGIN Theory.A6DoubleCoverFixedCertificate -/
namespace GLS3.Chapter5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem a6ExceptionalFixedCertificate (r : Fin 144) (s : Fin 5) :
    (a6ExceptionalConjugator⁻¹ *
      (a6DoubleCoverNormalForm (r, s) : Perm144) *
      a6ExceptionalConjugator) 0 =
      (a6DoubleCoverNormalForm (r, s) : Perm144) 0 →
    (r, s) ∈ a6ExceptionalFixedNormalIndices := by
  fin_cases r <;> fin_cases s <;> decide +revert +kernel

public theorem a6ExceptionalFixedNormalIndex_complete
    (x : Fin 144 × Fin 5)
    (h : a6ExceptionalConjugator⁻¹ *
      (a6DoubleCoverNormalForm x : Perm144) * a6ExceptionalConjugator =
      (a6DoubleCoverNormalForm x : Perm144)) :
    x ∈ a6ExceptionalFixedNormalIndices := by
  rcases x with ⟨r, s⟩
  apply a6ExceptionalFixedCertificate r s
  exact congrArg (fun g : Perm144 => g 0) h

end GLS3.Chapter5
/- END Theory.A6DoubleCoverFixedCertificate -/

/- BEGIN Theory.A6DoubleCoverFixedSubgroup -/
namespace GLS3.Chapter5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

@[reducible, expose] public def a6ExceptionalFixedGeneratorPerm : Perm144 :=
  a6DoubleCoverGen2 * a6DoubleCoverGen1 ^ 2 *
    a6DoubleCoverGen2⁻¹ * a6DoubleCoverGen1⁻¹

public theorem a6ExceptionalFixedGeneratorPerm_mem :
    a6ExceptionalFixedGeneratorPerm ∈ a6DoubleCoverPermutationSubgroup := by
  exact a6DoubleCoverPermutationSubgroup.mul_mem
    (a6DoubleCoverPermutationSubgroup.mul_mem
      (a6DoubleCoverPermutationSubgroup.mul_mem
        (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (a6DoubleCoverPermutationSubgroup.pow_mem
          (Subgroup.subset_closure (Set.mem_insert _ _)) 2))
      (a6DoubleCoverPermutationSubgroup.inv_mem
        (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
    (a6DoubleCoverPermutationSubgroup.inv_mem
      (Subgroup.subset_closure (Set.mem_insert _ _)))

@[expose] public def a6ExceptionalFixedGenerator :
    a6DoubleCoverPermutationSubgroup :=
  ⟨a6ExceptionalFixedGeneratorPerm, a6ExceptionalFixedGeneratorPerm_mem⟩

public theorem a6ExceptionalFixedGeneratorPerm_fixed :
    a6ExceptionalConjugator⁻¹ * a6ExceptionalFixedGeneratorPerm *
        a6ExceptionalConjugator = a6ExceptionalFixedGeneratorPerm := by
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

public theorem a6ExceptionalFixedGenerator_fixed :
    a6ExceptionalConjugatorLiftAut a6ExceptionalFixedGenerator =
      a6ExceptionalFixedGenerator := by
  apply Subtype.ext
  rw [a6ExceptionalConjugatorLiftAut_apply]
  exact a6ExceptionalFixedGeneratorPerm_fixed

public theorem a6ExceptionalFixedGeneratorPerm_order :
    orderOf a6ExceptionalFixedGeneratorPerm = 10 := by
  apply (orderOf_eq_iff (by decide : 0 < 10)).2
  constructor
  · apply Equiv.ext
    intro x
    fin_cases x <;> decide +revert +kernel
  · intro m hm hm0 h
    have h0 := Equiv.congr_fun h (0 : Fin 144)
    interval_cases m <;> norm_num at hm0
    all_goals first
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 1) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 2) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 3) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 4) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 5) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 6) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 7) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 8) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0
      | exact (show (a6ExceptionalFixedGeneratorPerm ^ 9) 0 ≠
          (1 : Perm144) 0 by decide +kernel) h0

public theorem a6ExceptionalFixedGenerator_order :
    orderOf a6ExceptionalFixedGenerator = 10 := by
  exact (orderOf_injective a6DoubleCoverPermutationSubgroup.subtype
    a6DoubleCoverPermutationSubgroup.subtype_injective
    a6ExceptionalFixedGenerator).symm.trans
      a6ExceptionalFixedGeneratorPerm_order

private noncomputable def a6ExceptionalFixedPacking :
    automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut →
      ↥a6ExceptionalFixedNormalIndices := fun g => by
  let x := a6DoubleCoverNormalFormEquiv.symm g.1
  have hx : a6DoubleCoverNormalForm x = g.1 := by
    rw [← a6DoubleCoverNormalFormEquiv_apply]
    exact a6DoubleCoverNormalFormEquiv.apply_symm_apply g.1
  have hfixed := congrArg
    (fun h : a6DoubleCoverPermutationSubgroup => (h : Perm144)) g.property
  rw [a6ExceptionalConjugatorLiftAut_apply] at hfixed
  refine ⟨x, a6ExceptionalFixedNormalIndex_complete x ?_⟩
  simpa [hx] using hfixed

private theorem __ch5_A6DoubleCoverFixedSubgroup_a6ExceptionalFixedPacking_injective :
    Function.Injective a6ExceptionalFixedPacking := by
  intro g h hgh
  have hindex : a6DoubleCoverNormalFormEquiv.symm g.1 =
      a6DoubleCoverNormalFormEquiv.symm h.1 :=
    congrArg Subtype.val hgh
  apply Subtype.ext
  exact a6DoubleCoverNormalFormEquiv.symm.injective hindex

public theorem a6ExceptionalFixedSubgroup_card_le_ten :
    Nat.card (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) ≤ 10 := by
  let : Fintype (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) :=
    Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective a6ExceptionalFixedPacking
    __ch5_A6DoubleCoverFixedSubgroup_a6ExceptionalFixedPacking_injective
  have hcod : Fintype.card ↥a6ExceptionalFixedNormalIndices = 10 := by
    rw [Fintype.card_coe, a6ExceptionalFixedNormalIndices_card]
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans_eq hcod

@[expose] public def a6ExceptionalFixedGeneratorInFixed :
    automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut :=
  ⟨a6ExceptionalFixedGenerator, a6ExceptionalFixedGenerator_fixed⟩

public theorem a6ExceptionalFixedGeneratorInFixed_order :
    orderOf a6ExceptionalFixedGeneratorInFixed = 10 := by
  exact (orderOf_injective
    (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut).subtype
    (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut).subtype_injective
    a6ExceptionalFixedGeneratorInFixed).symm.trans
      a6ExceptionalFixedGenerator_order

public theorem a6ExceptionalFixedSubgroup_card :
    Nat.card (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) = 10 := by
  have hdiv : 10 ∣ Nat.card
      (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) := by
    rw [← a6ExceptionalFixedGeneratorInFixed_order,
      ← Nat.card_zpowers a6ExceptionalFixedGeneratorInFixed]
    have hd := Subgroup.card_dvd_of_le
      (show Subgroup.zpowers a6ExceptionalFixedGeneratorInFixed ≤
        (⊤ : Subgroup
          (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut)) from le_top)
    rw [Subgroup.card_top] at hd
    exact hd
  have hpos : 0 < Nat.card
      (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) := Nat.card_pos
  have hle := a6ExceptionalFixedSubgroup_card_le_ten
  omega

public theorem a6ExceptionalFixedSubgroup_isCyclic :
    IsCyclic (automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut) := by
  apply isCyclic_iff_exists_orderOf_eq_natCard.mpr
  exact ⟨a6ExceptionalFixedGeneratorInFixed,
    a6ExceptionalFixedGeneratorInFixed_order.trans
      a6ExceptionalFixedSubgroup_card.symm⟩

public noncomputable def a6ExceptionalFixedSubgroupMulEquivZModTen :
    automorphismFixedSubgroup a6ExceptionalConjugatorLiftAut ≃*
      Multiplicative (ZMod 10) :=
  (a6ExceptionalFixedSubgroup_card ▸
    zmodCyclicMulEquiv a6ExceptionalFixedSubgroup_isCyclic).symm

end GLS3.Chapter5
/- END Theory.A6DoubleCoverFixedSubgroup -/
