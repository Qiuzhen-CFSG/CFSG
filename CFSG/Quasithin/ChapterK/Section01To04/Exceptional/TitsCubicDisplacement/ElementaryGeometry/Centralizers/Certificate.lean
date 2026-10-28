module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoEnumeration
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Mathlib.Tactic.FinCases
/-!
# A finite bound for Tits involutions avoiding the short-root class

The square-one test at point zero places every passing Sylow normal form in
a list of 28 indices or one of 116 rows below. Each row gives a word of length
at most six conjugating the literal s4 to that normal form. All word identities are
checked at the certified faithful three-point base. Thus every square-one
element avoiding the s4 class belongs to the remaining list of 28 indices.
Injecting any subgroup of such elements into this list bounds its order by 28.

The checks use the existing packed Parrott permutations. The rows are witnesses,
not assumptions: both coverage and conjugacy are checked by Lean's kernel.
Source: Parrott (1972), p.683, and the repository's ATLAS degree-1600 model;
application: GM04 Lemmas 2.3 and 8.8, internal pp.6 and 57, and
Aschbacher–Smith K.3, printed p.457. See `Centralizers/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Centralizers.Certificate
open Tits Tits.Atlas1600ParrottData Tits.Atlas1600SylowTwoCertificate
open Tits.OuterOddSubgroups.OverlapCentralizers

private def fastNormalForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) *
    Packed.perm 3 ^ (n.val / 2 % 2) *
    Packed.perm 4 ^ (n.val / 4 % 4) *
    Packed.perm 5 ^ (n.val / 16 % 2) *
    Packed.perm 6 ^ (n.val / 32 % 4) *
    Packed.perm 7 ^ (n.val / 128 % 2) *
    Packed.perm 8 ^ (n.val / 256 % 4) *
    Packed.perm 9 ^ (n.val / 1024 % 2)

private def allowed : List (Fin 2048) :=
  [0, 1, 10, 11, 65, 66, 73, 74, 80, 82, 89, 91, 523, 528,
   559, 564, 577, 602, 622, 629, 649, 665, 676, 692, 707, 723, 741, 757]

private def rows : List (Fin 2048 × List (Fin 10)) :=
  [(2, [ 1, 0 ]),
  (3, [ 1, 0, 4 ]),
  (8, [ 1, 0, 8 ]),
  (9, [ 6, 1, 0 ]),
  (16, [  ]),
  (17, [ 1, 0, 2, 0 ]),
  (18, [ 1, 4, 0 ]),
  (19, [ 1, 0, 8, 0 ]),
  (24, [ 1, 2, 0, 4 ]),
  (25, [ 8, 1, 0 ]),
  (26, [ 1, 8, 0, 4 ]),
  (27, [ 4 ]),
  (64, [ 1, 4, 0, 4 ]),
  (67, [ 1, 2, 0 ]),
  (72, [ 8, 8, 1, 0 ]),
  (75, [ 8, 1, 0, 4 ]),
  (81, [ 1, 4 ]),
  (83, [ 1, 8, 0 ]),
  (88, [ 8, 1, 2, 0 ]),
  (90, [ 8 ]),
  (128, [ 0 ]),
  (130, [ 9, 1, 4, 0 ]),
  (137, [ 4, 9, 1, 0 ]),
  (139, [ 2, 0 ]),
  (144, [ 4, 0 ]),
  (146, [ 9, 1, 0 ]),
  (153, [ 2, 9, 1, 0 ]),
  (155, [ 8, 0 ]),
  (193, [ 8, 4, 0 ]),
  (195, [ 6, 9, 1, 0 ]),
  (200, [ 9, 8, 1, 0 ]),
  (202, [ 9, 2, 0 ]),
  (209, [ 6, 0 ]),
  (211, [ 9, 1, 2, 0 ]),
  (216, [ 9, 6, 1, 0 ]),
  (218, [ 6, 2, 0 ]),
  (512, [ 4, 9, 1, 0, 4 ]),
  (539, [ 9, 1, 4, 0, 4 ]),
  (548, [ 0, 8, 0 ]),
  (575, [ 0, 4 ]),
  (586, [ 9, 1, 0, 2, 0 ]),
  (593, [ 9, 8, 1, 0, 4 ]),
  (613, [ 2, 0, 4 ]),
  (638, [ 0, 8 ]),
  (642, [ 9, 1, 0, 8 ]),
  (658, [ 2, 9, 1, 0, 4 ]),
  (687, [ 8, 0, 4 ]),
  (703, [ 6, 0, 4 ]),
  (712, [ 9, 1, 0, 4 ]),
  (728, [ 9, 1, 0, 8, 0 ]),
  (750, [ 0, 2, 0 ]),
  (766, [ 4, 0, 4 ]),
  (1024, [ 0, 1, 0 ]),
  (1040, [ 3, 0, 1, 4, 0 ]),
  (1070, [ 4, 9, 6, 0, 1, 0 ]),
  (1077, [ 8, 6, 2, 0, 1, 0 ]),
  (1089, [ 0, 1, 2, 0 ]),
  (1105, [ 0, 6, 9, 1, 0 ]),
  (1135, [ 0, 8, 0, 1, 0 ]),
  (1140, [ 4, 2, 8, 0, 1, 0 ]),
  (1152, [ 0, 1, 4, 0 ]),
  (1168, [ 3, 0, 1, 0 ]),
  (1189, [ 2, 0, 6, 1, 0 ]),
  (1214, [ 9, 2, 0, 6, 1, 0 ]),
  (1217, [ 0, 1, 8, 0 ]),
  (1233, [ 3, 0, 1, 2, 0 ]),
  (1252, [ 7, 2, 0, 6, 1, 0 ]),
  (1279, [ 8, 4, 2, 0, 1, 0 ]),
  (1284, [ 9, 4, 2, 0, 1, 0 ]),
  (1300, [ 5, 8, 0, 1, 0 ]),
  (1321, [ 5, 6, 0, 1, 0 ]),
  (1330, [ 4, 3, 0, 1, 0 ]),
  (1349, [ 3, 0, 2, 0, 1, 0 ]),
  (1365, [ 8, 0, 1, 0 ]),
  (1384, [ 6, 0, 1, 0 ]),
  (1395, [ 5, 4, 3, 0, 1, 0 ]),
  (1423, [ 8, 3, 0, 1, 0 ]),
  (1439, [ 0, 2, 0, 1, 0 ]),
  (1449, [ 5, 4, 0, 1, 0 ]),
  (1458, [ 3, 6, 0, 1, 0 ]),
  (1486, [ 2, 8, 2, 0, 1, 0 ]),
  (1502, [ 8, 0, 1, 4, 0 ]),
  (1512, [ 4, 0, 1, 0 ]),
  (1523, [ 6, 3, 0, 1, 0 ]),
  (1546, [ 9, 2, 0, 1, 0 ]),
  (1562, [ 7, 2, 0, 1, 0 ]),
  (1572, [ 4, 8, 0, 1, 0 ]),
  (1599, [ 0, 8, 1, 0 ]),
  (1611, [ 4, 6, 0, 1, 0 ]),
  (1627, [ 2, 0, 1, 0 ]),
  (1637, [ 3, 0, 6, 1, 0 ]),
  (1662, [ 0, 8, 1, 2, 0 ]),
  (1674, [ 4, 4, 0, 1, 0 ]),
  (1690, [ 2, 0, 1, 8, 0 ]),
  (1711, [ 3, 0, 8, 1, 0 ]),
  (1716, [ 0, 8, 8, 1, 0 ]),
  (1739, [ 3, 2, 0, 1, 0 ]),
  (1755, [ 6, 4, 0, 1, 0 ]),
  (1774, [ 0, 4, 9, 1, 0 ]),
  (1781, [ 0, 6, 1, 0 ]),
  (1797, [ 8, 3, 2, 0, 1, 0 ]),
  (1813, [ 9, 6, 0, 1, 0 ]),
  (1832, [ 9, 0, 2, 0, 1, 0 ]),
  (1843, [ 8, 0, 8, 1, 0 ]),
  (1860, [ 2, 8, 0, 1, 0 ]),
  (1876, [ 0, 6, 3, 0, 1, 0 ]),
  (1897, [ 0, 4, 4, 0, 1, 0 ]),
  (1906, [ 6, 2, 0, 1, 0 ]),
  (1934, [ 6, 0, 6, 1, 0 ]),
  (1950, [ 8, 7, 2, 0, 1, 0 ]),
  (1960, [ 3, 6, 2, 0, 1, 0 ]),
  (1971, [ 5, 4, 2, 0, 1, 0 ]),
  (1999, [ 4, 0, 8, 1, 0 ]),
  (2015, [ 8, 2, 0, 1, 0 ]),
  (2025, [ 9, 8, 0, 1, 0 ]),
  (2034, [ 4, 2, 0, 1, 0 ])]

private def squareTest (n : Fin 2048) : Bool :=
  let x := fastNormalForm n
  (x (x 0) == 0)

private def rowTest (r : Fin 2048 × List (Fin 10)) : Bool :=
  let x := fastNormalForm r.1
  let w := (r.2.map Packed.perm).prod
  [0, 1, 2].all (fun p : Fin 1600 => x (w p) == w (Packed.perm 5 p))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem coverage : ∀ n : Fin 2048, squareTest n = true →
    n ∈ allowed ∨ n ∈ rows.map Prod.fst := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem rows_checked : rows.all rowTest = true := by decide +kernel

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

private theorem word_val (w : List (Fin 10)) : (word w).val = (w.map Packed.perm).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (generator i).val * (word w).val = Packed.perm i * (w.map Packed.perm).prod
    rw [generator_val, ih]

private theorem nf_val (n : Fin 2048) : (atlas1600SylowTwoNormalForm n).val = fastNormalForm n := by
  rw [fastNormalForm_eq]
  exact atlas1600SylowTwoNormalForm_val n

private theorem rows_conjugate (i : Fin 2048) (w : List (Fin 10)) (h : (i, w) ∈ rows) :
    IsConj (atlas1600ParrottAssignment .s4) (atlas1600SylowTwoNormalForm i) := by
  have ht := List.all_eq_true.mp rows_checked (i, w) h
  have he : atlas1600SylowTwoNormalForm i * word w =
      word w * atlas1600ParrottAssignment .s4 := by
    apply Tits.ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
    all_goals
      simp only [show ∀ x y : Atlas1600Group, (x * y).val = x.val * y.val from fun _ _ => rfl,
        Equiv.Perm.mul_apply, nf_val, word_val,
        (show (atlas1600ParrottAssignment .s4).val = Packed.perm 5 from generator_val 5)]
      exact beq_iff_eq.mp (List.all_eq_true.mp ht _ (by simp))
  exact isConj_iff.mpr ⟨word w, mul_inv_eq_iff_eq_mul.mpr he.symm⟩

private theorem mem_allowed (i : Fin 2048) (h2 : atlas1600SylowTwoNormalForm i ^ 2 = 1)
    (hav : ¬ IsConj (atlas1600ParrottAssignment .s4) (atlas1600SylowTwoNormalForm i)) :
    i ∈ allowed := by
  have hs : squareTest i = true := by
    have hv := congrArg (fun g : Atlas1600Group => g.val) h2
    change (atlas1600SylowTwoNormalForm i).val ^ 2 = 1 at hv
    rw [nf_val] at hv
    have hp (p : Fin 1600) := congrArg (fun g : Equiv.Perm (Fin 1600) => g p) hv
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at hp
    simp only [squareTest, hp, beq_self_eq_true]
  rcases coverage i hs with h | h
  · exact h
  · obtain ⟨⟨j, w⟩, hj, he⟩ := List.mem_map.mp h
    change j = i at he
    subst j
    exact (hav (rows_conjugate i w hj)).elim

/-- The checked Sylow list bounds every subgroup consisting of square-one
elements and avoiding the literal short-root conjugacy class. -/
theorem card_le_twenty_eight (K : Subgroup Atlas1600Group)
    (hK : K ≤ atlas1600SylowTwoSubgroup)
    (h2 : ∀ k ∈ K, k ^ 2 = 1)
    (hav : ∀ k ∈ K, ¬ IsConj (atlas1600ParrottAssignment .s4) k) :
    Nat.card K ≤ 28 := by
  classical
  let code (k : K) : Fin 2048 := atlas1600SylowTwoEquiv.symm ⟨k.val, hK k.property⟩
  have hcode (k : K) : atlas1600SylowTwoNormalForm (code k) = k.val := by
    simpa only [atlas1600SylowTwoEquiv_apply, code] using
      congrArg Subtype.val (atlas1600SylowTwoEquiv.apply_symm_apply ⟨k.val, hK k.property⟩)
  have hmem (k : K) : code k ∈ allowed := by
    apply mem_allowed
    · rw [hcode]; exact h2 k.val k.property
    · rw [hcode]; exact hav k.val k.property
  let f : K → {i : Fin 2048 // i ∈ allowed} := fun k => ⟨code k, hmem k⟩
  have hi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    rw [← hcode a, ← hcode b]
    exact congrArg atlas1600SylowTwoNormalForm (congrArg Subtype.val he)
  have hc : Nat.card {i : Fin 2048 // i ∈ allowed} = 28 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (Nat.card_le_card_of_injective f hi).trans hc.le

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Centralizers.Certificate
