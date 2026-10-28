module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitArithmetic.Data

/-!
# Two-term rows of the ambient Lyons involution

The 201 nonzero entries of ambient A occupy at most two positions in each row.
The checked natural-number identity below proves the sparse description against
its original ATLAS entries, independently of the packed-column conversion.
Source: `../Atlas111Source/LyG1-f5r111B0.m1`; see the README there for attribution.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitArithmetic
open Atlas111Certificate

/-- Positions and coefficients of term 1; missing terms have coefficient zero. -/
def aTerm1 (k : ℕ) : ℕ × ℕ :=
  if k < 55 then
    if k < 27 then
      if k < 13 then
        if k < 6 then
          if k < 3 then
            if k < 1 then
              (0, 2)
            else
              if k < 2 then
                (1, 2)
              else
                (2, 2)
          else
            if k < 4 then
              (3, 2)
            else
              if k < 5 then
                (4, 2)
              else
                (5, 2)
        else
          if k < 9 then
            if k < 7 then
              (6, 2)
            else
              if k < 8 then
                (7, 2)
              else
                (8, 2)
          else
            if k < 11 then
              if k < 10 then
                (9, 2)
              else
                (10, 2)
            else
              if k < 12 then
                (11, 2)
              else
                (12, 2)
      else
        if k < 20 then
          if k < 16 then
            if k < 14 then
              (13, 2)
            else
              if k < 15 then
                (14, 2)
              else
                (15, 2)
          else
            if k < 18 then
              if k < 17 then
                (16, 2)
              else
                (17, 2)
            else
              if k < 19 then
                (18, 2)
              else
                (19, 2)
        else
          if k < 23 then
            if k < 21 then
              (20, 2)
            else
              if k < 22 then
                (21, 2)
              else
                (22, 2)
          else
            if k < 25 then
              if k < 24 then
                (23, 2)
              else
                (24, 2)
            else
              if k < 26 then
                (25, 2)
              else
                (26, 2)
    else
      if k < 41 then
        if k < 34 then
          if k < 30 then
            if k < 28 then
              (27, 2)
            else
              if k < 29 then
                (28, 2)
              else
                (29, 2)
          else
            if k < 32 then
              if k < 31 then
                (30, 2)
              else
                (31, 2)
            else
              if k < 33 then
                (32, 2)
              else
                (33, 2)
        else
          if k < 37 then
            if k < 35 then
              (34, 2)
            else
              if k < 36 then
                (35, 2)
              else
                (36, 2)
          else
            if k < 39 then
              if k < 38 then
                (37, 2)
              else
                (38, 2)
            else
              if k < 40 then
                (39, 2)
              else
                (40, 2)
      else
        if k < 48 then
          if k < 44 then
            if k < 42 then
              (41, 2)
            else
              if k < 43 then
                (42, 2)
              else
                (43, 2)
          else
            if k < 46 then
              if k < 45 then
                (44, 2)
              else
                (45, 1)
            else
              if k < 47 then
                (46, 1)
              else
                (47, 1)
        else
          if k < 51 then
            if k < 49 then
              (48, 1)
            else
              if k < 50 then
                (49, 1)
              else
                (50, 1)
          else
            if k < 53 then
              if k < 52 then
                (51, 1)
              else
                (52, 1)
            else
              if k < 54 then
                (53, 1)
              else
                (54, 1)
  else
    if k < 83 then
      if k < 69 then
        if k < 62 then
          if k < 58 then
            if k < 56 then
              (0, 1)
            else
              if k < 57 then
                (1, 1)
              else
                (2, 1)
          else
            if k < 60 then
              if k < 59 then
                (3, 1)
              else
                (4, 1)
            else
              if k < 61 then
                (5, 1)
              else
                (6, 1)
        else
          if k < 65 then
            if k < 63 then
              (7, 1)
            else
              if k < 64 then
                (8, 1)
              else
                (9, 1)
          else
            if k < 67 then
              if k < 66 then
                (10, 1)
              else
                (11, 1)
            else
              if k < 68 then
                (12, 1)
              else
                (13, 1)
      else
        if k < 76 then
          if k < 72 then
            if k < 70 then
              (14, 1)
            else
              if k < 71 then
                (15, 1)
              else
                (16, 1)
          else
            if k < 74 then
              if k < 73 then
                (17, 1)
              else
                (18, 1)
            else
              if k < 75 then
                (19, 1)
              else
                (20, 1)
        else
          if k < 79 then
            if k < 77 then
              (21, 1)
            else
              if k < 78 then
                (22, 1)
              else
                (23, 1)
          else
            if k < 81 then
              if k < 80 then
                (24, 1)
              else
                (25, 1)
            else
              if k < 82 then
                (26, 1)
              else
                (27, 1)
    else
      if k < 97 then
        if k < 90 then
          if k < 86 then
            if k < 84 then
              (28, 1)
            else
              if k < 85 then
                (29, 1)
              else
                (30, 1)
          else
            if k < 88 then
              if k < 87 then
                (31, 1)
              else
                (32, 1)
            else
              if k < 89 then
                (33, 1)
              else
                (34, 1)
        else
          if k < 93 then
            if k < 91 then
              (35, 1)
            else
              if k < 92 then
                (36, 1)
              else
                (37, 1)
          else
            if k < 95 then
              if k < 94 then
                (38, 1)
              else
                (39, 1)
            else
              if k < 96 then
                (40, 1)
              else
                (41, 1)
      else
        if k < 104 then
          if k < 100 then
            if k < 98 then
              (42, 1)
            else
              if k < 99 then
                (43, 1)
              else
                (44, 1)
          else
            if k < 102 then
              if k < 101 then
                (100, 4)
              else
                (101, 4)
            else
              if k < 103 then
                (102, 4)
              else
                (103, 4)
        else
          if k < 107 then
            if k < 105 then
              (104, 4)
            else
              if k < 106 then
                (105, 4)
              else
                (106, 4)
          else
            if k < 109 then
              if k < 108 then
                (107, 4)
              else
                (108, 4)
            else
              if k < 110 then
                (109, 4)
              else
                (110, 4)

/-- Positions and coefficients of term 2; missing terms have coefficient zero. -/
def aTerm2 (k : ℕ) : ℕ × ℕ :=
  if k < 55 then
    if k < 27 then
      if k < 13 then
        if k < 6 then
          if k < 3 then
            if k < 1 then
              (55, 2)
            else
              if k < 2 then
                (56, 2)
              else
                (57, 2)
          else
            if k < 4 then
              (58, 2)
            else
              if k < 5 then
                (59, 2)
              else
                (60, 2)
        else
          if k < 9 then
            if k < 7 then
              (61, 2)
            else
              if k < 8 then
                (62, 2)
              else
                (63, 2)
          else
            if k < 11 then
              if k < 10 then
                (64, 2)
              else
                (65, 2)
            else
              if k < 12 then
                (66, 2)
              else
                (67, 2)
      else
        if k < 20 then
          if k < 16 then
            if k < 14 then
              (68, 2)
            else
              if k < 15 then
                (69, 2)
              else
                (70, 2)
          else
            if k < 18 then
              if k < 17 then
                (71, 2)
              else
                (72, 2)
            else
              if k < 19 then
                (73, 2)
              else
                (74, 2)
        else
          if k < 23 then
            if k < 21 then
              (75, 2)
            else
              if k < 22 then
                (76, 2)
              else
                (77, 2)
          else
            if k < 25 then
              if k < 24 then
                (78, 2)
              else
                (79, 2)
            else
              if k < 26 then
                (80, 2)
              else
                (81, 2)
    else
      if k < 41 then
        if k < 34 then
          if k < 30 then
            if k < 28 then
              (82, 2)
            else
              if k < 29 then
                (83, 2)
              else
                (84, 2)
          else
            if k < 32 then
              if k < 31 then
                (85, 2)
              else
                (86, 2)
            else
              if k < 33 then
                (87, 2)
              else
                (88, 2)
        else
          if k < 37 then
            if k < 35 then
              (89, 2)
            else
              if k < 36 then
                (90, 2)
              else
                (91, 2)
          else
            if k < 39 then
              if k < 38 then
                (92, 2)
              else
                (93, 2)
            else
              if k < 40 then
                (94, 2)
              else
                (95, 2)
      else
        if k < 48 then
          if k < 44 then
            if k < 42 then
              (96, 2)
            else
              if k < 43 then
                (97, 2)
              else
                (98, 2)
          else
            if k < 46 then
              if k < 45 then
                (99, 2)
              else
                (0, 0)
            else
              if k < 47 then
                (0, 0)
              else
                (0, 0)
        else
          if k < 51 then
            if k < 49 then
              (0, 0)
            else
              if k < 50 then
                (0, 0)
              else
                (0, 0)
          else
            if k < 53 then
              if k < 52 then
                (0, 0)
              else
                (0, 0)
            else
              if k < 54 then
                (0, 0)
              else
                (0, 0)
  else
    if k < 83 then
      if k < 69 then
        if k < 62 then
          if k < 58 then
            if k < 56 then
              (55, 3)
            else
              if k < 57 then
                (56, 3)
              else
                (57, 3)
          else
            if k < 60 then
              if k < 59 then
                (58, 3)
              else
                (59, 3)
            else
              if k < 61 then
                (60, 3)
              else
                (61, 3)
        else
          if k < 65 then
            if k < 63 then
              (62, 3)
            else
              if k < 64 then
                (63, 3)
              else
                (64, 3)
          else
            if k < 67 then
              if k < 66 then
                (65, 3)
              else
                (66, 3)
            else
              if k < 68 then
                (67, 3)
              else
                (68, 3)
      else
        if k < 76 then
          if k < 72 then
            if k < 70 then
              (69, 3)
            else
              if k < 71 then
                (70, 3)
              else
                (71, 3)
          else
            if k < 74 then
              if k < 73 then
                (72, 3)
              else
                (73, 3)
            else
              if k < 75 then
                (74, 3)
              else
                (75, 3)
        else
          if k < 79 then
            if k < 77 then
              (76, 3)
            else
              if k < 78 then
                (77, 3)
              else
                (78, 3)
          else
            if k < 81 then
              if k < 80 then
                (79, 3)
              else
                (80, 3)
            else
              if k < 82 then
                (81, 3)
              else
                (82, 3)
    else
      if k < 97 then
        if k < 90 then
          if k < 86 then
            if k < 84 then
              (83, 3)
            else
              if k < 85 then
                (84, 3)
              else
                (85, 3)
          else
            if k < 88 then
              if k < 87 then
                (86, 3)
              else
                (87, 3)
            else
              if k < 89 then
                (88, 3)
              else
                (89, 3)
        else
          if k < 93 then
            if k < 91 then
              (90, 3)
            else
              if k < 92 then
                (91, 3)
              else
                (92, 3)
          else
            if k < 95 then
              if k < 94 then
                (93, 3)
              else
                (94, 3)
            else
              if k < 96 then
                (95, 3)
              else
                (96, 3)
      else
        if k < 104 then
          if k < 100 then
            if k < 98 then
              (97, 3)
            else
              if k < 99 then
                (98, 3)
              else
                (99, 3)
          else
            if k < 102 then
              if k < 101 then
                (0, 0)
              else
                (0, 0)
            else
              if k < 103 then
                (0, 0)
              else
                (0, 0)
        else
          if k < 107 then
            if k < 105 then
              (0, 0)
            else
              if k < 106 then
                (0, 0)
              else
                (0, 0)
          else
            if k < 109 then
              if k < 108 then
                (0, 0)
              else
                (0, 0)
            else
              if k < 110 then
                (0, 0)
              else
                (0, 0)

def aSupport1 (i : Fin 111) : Fin 111 × ℕ :=
  (Fin.ofNat 111 (aTerm1 i).1, (aTerm1 i).2)

def aSupport2 (i : Fin 111) : Fin 111 × ℕ :=
  (Fin.ofNat 111 (aTerm2 i).1, (aTerm2 i).2)

/-- The sparse natural representative of A. -/
def sparseAEntry (i k : Fin 111) : ℕ :=
  (if k = (aSupport1 i).1 then (aSupport1 i).2 else 0) +
  (if k = (aSupport2 i).1 then (aSupport2 i).2 else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem sparseA_checked :
    allBelow 111 (fun i => allBelow 111 (fun k =>
      generatorEntry false k i == sparseAEntry (Fin.ofNat 111 i) (Fin.ofNat 111 k))) = true := by
  decide +kernel

theorem generatorEntry_eq_sparseA (i k : Fin 111) :
    generatorEntry false k i = sparseAEntry i k := by
  have h := allBelow_sound (allBelow_sound sparseA_checked i.val i.isLt) k.val k.isLt
  have hi : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  have hk : Fin.ofNat 111 k.val = k := by ext; exact Nat.mod_eq_of_lt k.isLt
  simpa only [hi, hk, beq_iff_eq] using h
end Lyons.OrderCertificate.PlaneOrbitArithmetic
