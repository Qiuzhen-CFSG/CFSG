module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Data
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoEnumeration
import Mathlib.Tactic

/-!
# The two marked root classes in the Tits Sylow subgroup

A point-zero square test leaves 144 of the 2048 proved Sylow normal forms,
including the identity. The remaining 143 rows carry actual conjugating
words: 27 for the long root and 116 for the short root. Every word equation
is checked on the established faithful three-point base. Coverage and row
checks are split into small blocks and checked by the kernel at default
heartbeat limits. The search script supplies only witnesses, not premises.

Source: Parrott (1972), section 5, p.683; GLS3 Table 2.4; Aschbacher--Smith
16.1.4, printed p.1171, and K.3, printed p.457.
-/

public section
namespace Tits.InvolutionRootGeometry.BinaryCoverage
open Tits Tits.Atlas1600ParrottData Tits.Atlas1600SylowTwoCertificate
open Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Tits.OuterOddSubgroups.OverlapCentralizers
private abbrev Row := Fin 2048 × Bool × List (Fin 10)
private def rows0 : List Row := [
  (1, true, []),
  (2, false, [1, 0]),
  (3, false, [1, 0, 4]),
  (8, false, [1, 0, 8]),
  (9, false, [6, 1, 0]),
  (10, true, [7]),
  (11, true, [0, 1]),
  (16, false, [])]
private def rows1 : List Row := [
  (17, false, [1, 0, 2, 0]),
  (18, false, [1, 4, 0]),
  (19, false, [1, 0, 8, 0]),
  (24, false, [1, 2, 0, 4]),
  (25, false, [8, 1, 0]),
  (26, false, [1, 8, 0, 4]),
  (27, false, [4]),
  (64, false, [1, 4, 0, 4])]
private def rows2 : List Row := [
  (65, true, [1, 0, 1]),
  (66, true, [9, 4, 9]),
  (67, false, [1, 2, 0]),
  (72, false, [8, 8, 1, 0]),
  (73, true, [1, 8, 1]),
  (74, true, [9, 0, 1]),
  (75, false, [8, 1, 0, 4]),
  (80, true, [8, 8])]
private def rows3 : List Row := [
  (81, false, [1, 4]),
  (82, true, [8]),
  (83, false, [1, 8, 0]),
  (88, false, [8, 1, 2, 0]),
  (89, true, [8, 7]),
  (90, false, [8]),
  (91, true, [1, 2, 1]),
  (128, false, [0])]
private def rows4 : List Row := [
  (130, false, [9, 1, 4, 0]),
  (137, false, [4, 9, 1, 0]),
  (139, false, [2, 0]),
  (144, false, [4, 0]),
  (146, false, [9, 1, 0]),
  (153, false, [2, 9, 1, 0]),
  (155, false, [8, 0]),
  (193, false, [8, 4, 0])]
private def rows5 : List Row := [
  (195, false, [6, 9, 1, 0]),
  (200, false, [9, 8, 1, 0]),
  (202, false, [9, 2, 0]),
  (209, false, [6, 0]),
  (211, false, [9, 1, 2, 0]),
  (216, false, [9, 6, 1, 0]),
  (218, false, [6, 2, 0]),
  (512, false, [4, 9, 1, 0, 4])]
private def rows6 : List Row := [
  (523, true, [2, 9]),
  (528, true, [9, 7]),
  (539, false, [9, 1, 4, 0, 4]),
  (548, false, [0, 8, 0]),
  (559, true, [4, 1]),
  (564, true, [8, 3, 1]),
  (575, false, [0, 4]),
  (577, true, [2, 9, 7])]
private def rows7 : List Row := [
  (586, false, [9, 1, 0, 2, 0]),
  (593, false, [9, 8, 1, 0, 4]),
  (602, true, [9]),
  (613, false, [2, 0, 4]),
  (622, true, [8, 2, 1]),
  (629, true, [8, 1]),
  (638, false, [0, 8]),
  (642, false, [9, 1, 0, 8])]
private def rows8 : List Row := [
  (649, true, [4, 9]),
  (658, false, [2, 9, 1, 0, 4]),
  (665, true, [9, 8]),
  (676, true, [2, 1]),
  (687, false, [8, 0, 4]),
  (692, true, [3, 1]),
  (703, false, [6, 0, 4]),
  (707, true, [6, 9])]
private def rows9 : List Row := [
  (712, false, [9, 1, 0, 4]),
  (723, true, [9, 8, 7]),
  (728, false, [9, 1, 0, 8, 0]),
  (741, true, [3, 2, 1]),
  (750, false, [0, 2, 0]),
  (757, true, [1]),
  (766, false, [4, 0, 4]),
  (1024, false, [0, 1, 0])]
private def rows10 : List Row := [
  (1040, false, [3, 0, 1, 4, 0]),
  (1070, false, [4, 9, 6, 0, 1, 0]),
  (1077, false, [8, 6, 2, 0, 1, 0]),
  (1089, false, [0, 1, 2, 0]),
  (1105, false, [0, 6, 9, 1, 0]),
  (1135, false, [0, 8, 0, 1, 0]),
  (1140, false, [4, 2, 8, 0, 1, 0]),
  (1152, false, [0, 1, 4, 0])]
private def rows11 : List Row := [
  (1168, false, [3, 0, 1, 0]),
  (1189, false, [2, 0, 6, 1, 0]),
  (1214, false, [9, 2, 0, 6, 1, 0]),
  (1217, false, [0, 1, 8, 0]),
  (1233, false, [3, 0, 1, 2, 0]),
  (1252, false, [7, 2, 0, 6, 1, 0]),
  (1279, false, [8, 4, 2, 0, 1, 0]),
  (1284, false, [9, 4, 2, 0, 1, 0])]
private def rows12 : List Row := [
  (1300, false, [5, 8, 0, 1, 0]),
  (1321, false, [5, 6, 0, 1, 0]),
  (1330, false, [4, 3, 0, 1, 0]),
  (1349, false, [3, 0, 2, 0, 1, 0]),
  (1365, false, [8, 0, 1, 0]),
  (1384, false, [6, 0, 1, 0]),
  (1395, false, [5, 4, 3, 0, 1, 0]),
  (1423, false, [8, 3, 0, 1, 0])]
private def rows13 : List Row := [
  (1439, false, [0, 2, 0, 1, 0]),
  (1449, false, [5, 4, 0, 1, 0]),
  (1458, false, [3, 6, 0, 1, 0]),
  (1486, false, [2, 8, 2, 0, 1, 0]),
  (1502, false, [8, 0, 1, 4, 0]),
  (1512, false, [4, 0, 1, 0]),
  (1523, false, [6, 3, 0, 1, 0]),
  (1546, false, [9, 2, 0, 1, 0])]
private def rows14 : List Row := [
  (1562, false, [7, 2, 0, 1, 0]),
  (1572, false, [4, 8, 0, 1, 0]),
  (1599, false, [0, 8, 1, 0]),
  (1611, false, [4, 6, 0, 1, 0]),
  (1627, false, [2, 0, 1, 0]),
  (1637, false, [3, 0, 6, 1, 0]),
  (1662, false, [0, 8, 1, 2, 0]),
  (1674, false, [4, 4, 0, 1, 0])]
private def rows15 : List Row := [
  (1690, false, [2, 0, 1, 8, 0]),
  (1711, false, [3, 0, 8, 1, 0]),
  (1716, false, [0, 8, 8, 1, 0]),
  (1739, false, [3, 2, 0, 1, 0]),
  (1755, false, [6, 4, 0, 1, 0]),
  (1774, false, [0, 4, 9, 1, 0]),
  (1781, false, [0, 6, 1, 0]),
  (1797, false, [8, 3, 2, 0, 1, 0])]
private def rows16 : List Row := [
  (1813, false, [9, 6, 0, 1, 0]),
  (1832, false, [9, 0, 2, 0, 1, 0]),
  (1843, false, [8, 0, 8, 1, 0]),
  (1860, false, [2, 8, 0, 1, 0]),
  (1876, false, [0, 6, 3, 0, 1, 0]),
  (1897, false, [0, 4, 4, 0, 1, 0]),
  (1906, false, [6, 2, 0, 1, 0]),
  (1934, false, [6, 0, 6, 1, 0])]
private def rows17 : List Row := [
  (1950, false, [8, 7, 2, 0, 1, 0]),
  (1960, false, [3, 6, 2, 0, 1, 0]),
  (1971, false, [5, 4, 2, 0, 1, 0]),
  (1999, false, [4, 0, 8, 1, 0]),
  (2015, false, [8, 2, 0, 1, 0]),
  (2025, false, [9, 8, 0, 1, 0]),
  (2034, false, [4, 2, 0, 1, 0])]
private def rows : List Row := rows0 ++ rows1 ++ rows2 ++ rows3 ++ rows4 ++ rows5 ++ rows6 ++ rows7 ++ rows8 ++ rows9 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17
private def squareTest (n : Fin 2048) : Bool :=
  fastNormalForm n (fastNormalForm n 0) == 0
private def rowTest (r : Row) : Bool :=
  let x := fastNormalForm r.1
  let w := (r.2.2.map Packed.perm).prod
  [0, 1, 2].all (fun p : Fin 1600 => x (w p) == w (Packed.perm (if r.2.1 then 2 else 5) p))
private def slice (b : Fin 32) (j : Fin 64) : Fin 2048 := ⟨64 * b.val + j.val, by omega⟩
private def Covered (n : Fin 2048) : Prop := squareTest n = true → n = 0 ∨ n ∈ rows.map Prod.fst
private instance (n : Fin 2048) : Decidable (Covered n) := inferInstanceAs (Decidable (_ → _ ∨ _))
set_option maxRecDepth 20000 in
private theorem rows0_checked : rows0.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows1_checked : rows1.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows2_checked : rows2.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows3_checked : rows3.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows4_checked : rows4.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows5_checked : rows5.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows6_checked : rows6.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows7_checked : rows7.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows8_checked : rows8.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows9_checked : rows9.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows10_checked : rows10.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows11_checked : rows11.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows12_checked : rows12.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows13_checked : rows13.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows14_checked : rows14.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows15_checked : rows15.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows16_checked : rows16.all rowTest = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem rows17_checked : rows17.all rowTest = true := by decide +kernel
private theorem rows_checked : rows.all rowTest = true := by
  simp only [rows, List.all_append, rows0_checked, rows1_checked, rows2_checked, rows3_checked, rows4_checked, rows5_checked, rows6_checked, rows7_checked, rows8_checked, rows9_checked, rows10_checked, rows11_checked, rows12_checked, rows13_checked, rows14_checked, rows15_checked, rows16_checked, rows17_checked]
  rfl
set_option maxRecDepth 20000 in
private theorem coverage0 : ∀ i : Fin 64, Covered (slice 0 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage1 : ∀ i : Fin 64, Covered (slice 1 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage2 : ∀ i : Fin 64, Covered (slice 2 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage3 : ∀ i : Fin 64, Covered (slice 3 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage4 : ∀ i : Fin 64, Covered (slice 4 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage5 : ∀ i : Fin 64, Covered (slice 5 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage6 : ∀ i : Fin 64, Covered (slice 6 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage7 : ∀ i : Fin 64, Covered (slice 7 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage8 : ∀ i : Fin 64, Covered (slice 8 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage9 : ∀ i : Fin 64, Covered (slice 9 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage10 : ∀ i : Fin 64, Covered (slice 10 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage11 : ∀ i : Fin 64, Covered (slice 11 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage12 : ∀ i : Fin 64, Covered (slice 12 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage13 : ∀ i : Fin 64, Covered (slice 13 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage14 : ∀ i : Fin 64, Covered (slice 14 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage15 : ∀ i : Fin 64, Covered (slice 15 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage16 : ∀ i : Fin 64, Covered (slice 16 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage17 : ∀ i : Fin 64, Covered (slice 17 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage18 : ∀ i : Fin 64, Covered (slice 18 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage19 : ∀ i : Fin 64, Covered (slice 19 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage20 : ∀ i : Fin 64, Covered (slice 20 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage21 : ∀ i : Fin 64, Covered (slice 21 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage22 : ∀ i : Fin 64, Covered (slice 22 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage23 : ∀ i : Fin 64, Covered (slice 23 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage24 : ∀ i : Fin 64, Covered (slice 24 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage25 : ∀ i : Fin 64, Covered (slice 25 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage26 : ∀ i : Fin 64, Covered (slice 26 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage27 : ∀ i : Fin 64, Covered (slice 27 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage28 : ∀ i : Fin 64, Covered (slice 28 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage29 : ∀ i : Fin 64, Covered (slice 29 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage30 : ∀ i : Fin 64, Covered (slice 30 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
set_option maxRecDepth 20000 in
private theorem coverage31 : ∀ i : Fin 64, Covered (slice 31 i) := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel
private theorem coverage (n : Fin 2048) : Covered n := by
  let b : Fin 32 := ⟨n.val / 64, by omega⟩
  let j : Fin 64 := ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : slice b j = n := Fin.ext (by dsimp [slice, b, j]; omega)
  rw [← he]
  have hb : ∀ b : Fin 32, ∀ j : Fin 64, Covered (slice b j) := by
    intro b
    fin_cases b
    · exact coverage0
    · exact coverage1
    · exact coverage2
    · exact coverage3
    · exact coverage4
    · exact coverage5
    · exact coverage6
    · exact coverage7
    · exact coverage8
    · exact coverage9
    · exact coverage10
    · exact coverage11
    · exact coverage12
    · exact coverage13
    · exact coverage14
    · exact coverage15
    · exact coverage16
    · exact coverage17
    · exact coverage18
    · exact coverage19
    · exact coverage20
    · exact coverage21
    · exact coverage22
    · exact coverage23
    · exact coverage24
    · exact coverage25
    · exact coverage26
    · exact coverage27
    · exact coverage28
    · exact coverage29
    · exact coverage30
    · exact coverage31
  exact hb b j

private theorem fastNormalForm_eq (n : Fin 2048) : fastNormalForm n = normalForm n := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, normalForm]

private def generator : Fin 10 → Atlas1600Group :=
  ![atlas1600ParrottAssignment .r1, atlas1600ParrottAssignment .r8,
    atlas1600ParrottAssignment .s1, atlas1600ParrottAssignment .s2,
    atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s4,
    atlas1600ParrottAssignment .s5, atlas1600ParrottAssignment .s6,
    atlas1600ParrottAssignment .s7, atlas1600ParrottAssignment .s8]

private theorem generator_val (i : Fin 10) : (generator i).val = Packed.perm i := by
  rw [Packed.perm_eq]
  fin_cases i <;> simp [generator, Packed.generator, atlas1600ParrottAssignment_val, permutation]

private def word (w : List (Fin 10)) : Atlas1600Group := (w.map generator).prod
private def root (b : Bool) : Atlas1600Group :=
  if b then atlas1600ParrottAssignment .s1 else atlas1600ParrottAssignment .s4

private theorem root_val (b : Bool) : (root b).val = Packed.perm (if b then 2 else 5) := by
  cases b
  · exact generator_val 5
  · exact generator_val 2

private theorem word_val (w : List (Fin 10)) : (word w).val = (w.map Packed.perm).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (generator i).val * (word w).val = Packed.perm i * (w.map Packed.perm).prod
    rw [generator_val, ih]

private theorem nf_val (n : Fin 2048) : (atlas1600SylowTwoNormalForm n).val = fastNormalForm n := by
  rw [fastNormalForm_eq]
  exact atlas1600SylowTwoNormalForm_val n

private theorem rows_conjugate (i : Fin 2048) (b : Bool) (w : List (Fin 10))
    (h : (i, b, w) ∈ rows) : IsConj (root b) (atlas1600SylowTwoNormalForm i) := by
  have ht := List.all_eq_true.mp rows_checked (i, b, w) h
  have he : atlas1600SylowTwoNormalForm i * word w = word w * root b := by
    apply threePoint_ext
    all_goals
      simp only [show ∀ x y : Atlas1600Group, (x * y).val = x.val * y.val from fun _ _ => rfl,
        Equiv.Perm.mul_apply, nf_val, word_val, root_val]
      exact beq_iff_eq.mp (List.all_eq_true.mp ht _ (by simp))
  exact isConj_iff.mpr ⟨word w, mul_inv_eq_iff_eq_mul.mpr he.symm⟩

/-- Every nonidentity square-one Sylow normal form is in one of the two
literal marked Parrott root classes, with all conjugators inside the group. -/
theorem normalForm_root_classes (i : Fin 2048)
    (h2 : atlas1600SylowTwoNormalForm i ^ 2 = 1)
    (hne : atlas1600SylowTwoNormalForm i ≠ 1) :
    IsConj (atlas1600ParrottAssignment .s1) (atlas1600SylowTwoNormalForm i) ∨
      IsConj (atlas1600ParrottAssignment .s4) (atlas1600SylowTwoNormalForm i) := by
  have hs : squareTest i = true := by
    have hv := congrArg (fun g : Atlas1600Group => g.val) h2
    change (atlas1600SylowTwoNormalForm i).val ^ 2 = 1 at hv
    rw [nf_val] at hv
    have hp := congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hv
    simpa only [squareTest, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      beq_iff_eq] using hp
  rcases coverage i hs with hi | hi
  · subst i
    exact (hne (Subtype.ext (by rw [nf_val]; change fastNormalForm 0 = 1; simp [fastNormalForm]))).elim
  · obtain ⟨⟨j, b, w⟩, hr, he⟩ := List.mem_map.mp hi
    change j = i at he
    subst j
    have hc := rows_conjugate i b w hr
    cases b
    · exact Or.inr hc
    · exact Or.inl hc

end Tits.InvolutionRootGeometry.BinaryCoverage
