module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction

/-!
# Twenty-five dimensions from exact middle-adjacent support

For a nonzero local highest vector with support `{1,2}`, the inactive
exchanges on coordinates `{0,1}` and `{3,4}` fix the vector. We choose
25 permutation translates and separate them by products of upper-root
differences. Each product kills the preceding vectors and takes its own
vector to a nonzero permutation translate.

Reordering the factors is essential: commuting root differences commute,
and the three factors for a rank-two upper unipotent group multiply to its
norm in any order. Here the necessary reorderings follow by expanding the
products and checking a permutation of the four or eight group elements.
The remaining steps are the upper-fixed and active rank-one relations,
conjugated through permutations and inactive exchanges.

All finite identities use kernel reduction. The certificate generator and
its input are in `source/`; no output of the search is trusted as a proof.
No irreducibility, faithfulness or highest-weight comparison is needed.

Source application: Guralnick–Malle, *Classification of 2F-modules, II*,
Lemma 4.2/Table 6, pp.22–23, and Proposition 4.8(3B), pp.27–28;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
open scoped BigOperators
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.MiddlePair
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V}
private theorem neg_eq_self (x : V) : -x = x := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  have hx : x + x = 0 := by
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh
  exact neg_eq_of_add_eq_zero_left hx
private theorem difference_apply_add (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) (t : Representation.SL5TenDimensional.Group) (x : V) :
    difference ρ t x = ρ t x + x := by
  change ρ t x - x = _
  rw [sub_eq_add_neg, neg_eq_self]

private def twoProducts (a b : Representation.SL5TenDimensional.Group) :
    Fin 4 → Representation.SL5TenDimensional.Group := ![a * b, a, b, 1]
private def threeProducts (a b c : Representation.SL5TenDimensional.Group) :
    Fin 8 → Representation.SL5TenDimensional.Group :=
  ![a * b * c, a * b, a * c, a, b * c, b, c, 1]
private theorem two_expansion (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) (a b : Representation.SL5TenDimensional.Group) (x : V) :
    difference ρ a (difference ρ b x) = ∑ i, ρ (twoProducts a b i) x := by
  simp only [difference_apply_add, map_add, ← apply_mul, twoProducts,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_one, Module.End.one_apply, add_zero]
  abel
private theorem three_expansion (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) (a b c : Representation.SL5TenDimensional.Group) (x : V) :
    difference ρ a (difference ρ b (difference ρ c x)) =
      ∑ i, ρ (threeProducts a b c i) x := by
  simp only [difference_apply_add, map_add, ← apply_mul, threeProducts,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_one, Module.End.one_apply, add_zero, mul_assoc]
  abel

private theorem reorder_two (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) (a b c d : Representation.SL5TenDimensional.Group)
    (q : Equiv.Perm (Fin 4)) (h : ∀ i, twoProducts a b i = twoProducts c d (q i))
    (x : V) : difference ρ a (difference ρ b x) = difference ρ c (difference ρ d x) := by
  rw [two_expansion, two_expansion]
  exact Fintype.sum_equiv q _ _ (fun i => congrArg (fun g => ρ g x) (h i))

private theorem reorder_three (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) (a b c d e f : Representation.SL5TenDimensional.Group)
    (q : Equiv.Perm (Fin 8)) (h : ∀ i, threeProducts a b c i = threeProducts d e f (q i))
    (x : V) : difference ρ a (difference ρ b (difference ρ c x)) =
      difference ρ d (difference ρ e (difference ρ f x)) := by
  rw [three_expansion, three_expansion]
  exact Fintype.sum_equiv q _ _ (fun i => congrArg (fun g => ρ g x) (h i))


variable {v : V} (h : LocalHighestVector ρ {1, 2} v)
include h

private def permutationSL (p : Equiv.Perm (Fin 5)) :
    Representation.SL5TenDimensional.Group :=
  ⟨(1 : Matrix (Fin 5) (Fin 5) (ZMod 2)).submatrix id p, by
    rw [Matrix.det_permute', Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp]
    all_goals decide⟩

private def w0 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide +kernel, by decide +kernel⟩
private def w1 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 1, 3, 4], ![0, 2, 1, 3, 4], by decide +kernel, by decide +kernel⟩
private def w2 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 3, 2, 4], ![0, 1, 3, 2, 4], by decide +kernel, by decide +kernel⟩
private def w3 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide +kernel, by decide +kernel⟩
private def w4 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 3, 1, 4], ![0, 3, 1, 2, 4], by decide +kernel, by decide +kernel⟩
private def w5 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 1, 2, 4], ![0, 2, 3, 1, 4], by decide +kernel, by decide +kernel⟩
private def w6 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide +kernel, by decide +kernel⟩
private def w7 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 0, 2, 4], ![2, 0, 3, 1, 4], by decide +kernel, by decide +kernel⟩
private def w8 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 3, 0, 4], ![3, 0, 1, 2, 4], by decide +kernel, by decide +kernel⟩
private def w9 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide +kernel, by decide +kernel⟩
private def w10 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 4, 1, 2, 3], ![0, 2, 3, 4, 1], by decide +kernel, by decide +kernel⟩
private def w11 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide +kernel, by decide +kernel⟩
private def w12 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide +kernel, by decide +kernel⟩
private def w13 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 4, 0, 2, 3], ![2, 0, 3, 4, 1], by decide +kernel, by decide +kernel⟩
private def w14 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 4, 2, 1, 3], ![0, 3, 2, 4, 1], by decide +kernel, by decide +kernel⟩
private def w15 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide +kernel, by decide +kernel⟩
private def w16 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], by decide +kernel, by decide +kernel⟩
private def w17 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 4, 0, 3], ![3, 0, 1, 4, 2], by decide +kernel, by decide +kernel⟩
private def w18 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 3, 1, 0, 4], ![3, 2, 0, 1, 4], by decide +kernel, by decide +kernel⟩
private def w19 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 4, 0, 1, 3], ![2, 3, 0, 4, 1], by decide +kernel, by decide +kernel⟩
private def w20 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 4, 3, 1, 2], ![0, 3, 4, 2, 1], by decide +kernel, by decide +kernel⟩
private def w21 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 4, 0, 2], ![3, 0, 4, 1, 2], by decide +kernel, by decide +kernel⟩
private def w22 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 4, 2, 0, 3], ![3, 0, 2, 4, 1], by decide +kernel, by decide +kernel⟩
private def w23 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 4, 3, 0, 2], ![3, 0, 4, 2, 1], by decide +kernel, by decide +kernel⟩
private def w24 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide +kernel, by decide +kernel⟩

attribute [local irreducible] w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24

omit h in
private theorem reorder0 (x : V) :
    difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (x)) =
    difference ρ (rootElement 0 1) (difference ρ (rootElement 0 3) (x)) := by
  apply reorder_two ρ (rootElement 0 3) (rootElement 0 1) (rootElement 0 1) (rootElement 0 3)
    ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder1 (x : V) :
    difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (x))) =
    difference ρ (rootElement 2 3) (difference ρ (rootElement 1 2) (difference ρ (rootElement 1 3) (x))) := by
  apply reorder_three ρ (rootElement 2 3) (rootElement 1 3) (rootElement 1 2) (rootElement 2 3) (rootElement 1 2) (rootElement 1 3)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder2 (x : V) :
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (x)) =
    difference ρ (rootElement 0 2) (difference ρ (rootElement 1 2) (x)) := by
  apply reorder_two ρ (rootElement 1 2) (rootElement 0 2) (rootElement 0 2) (rootElement 1 2)
    ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder3 (x : V) :
    difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (x))) =
    difference ρ (rootElement 2 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 1 4) (x))) := by
  apply reorder_three ρ (rootElement 2 4) (rootElement 1 4) (rootElement 1 2) (rootElement 2 4) (rootElement 1 2) (rootElement 1 4)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder4 (x : V) :
    difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 2 3) (difference ρ (rootElement 0 1) (difference ρ (rootElement 0 3) (x))) := by
  apply reorder_three ρ (rootElement 2 3) (rootElement 0 3) (rootElement 0 1) (rootElement 2 3) (rootElement 0 1) (rootElement 0 3)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder5 (x : V) :
    difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 0 1) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 3) (x))) := by
  apply reorder_three ρ (rootElement 2 3) (rootElement 0 3) (rootElement 0 1) (rootElement 0 1) (rootElement 0 3) (rootElement 2 3)
    ⟨![0, 4, 2, 6, 1, 5, 3, 7], ![0, 4, 2, 6, 1, 5, 3, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder6 (x : V) :
    difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (x)) =
    difference ρ (rootElement 1 3) (difference ρ (rootElement 1 4) (x)) := by
  apply reorder_two ρ (rootElement 1 4) (rootElement 1 3) (rootElement 1 3) (rootElement 1 4)
    ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder7 (x : V) :
    difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (x)) =
    difference ρ (rootElement 0 1) (difference ρ (rootElement 0 4) (x)) := by
  apply reorder_two ρ (rootElement 0 4) (rootElement 0 1) (rootElement 0 1) (rootElement 0 4)
    ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder8 (x : V) :
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (difference ρ (rootElement 1 2) (x))) := by
  apply reorder_three ρ (rootElement 1 2) (rootElement 0 2) (rootElement 0 1) (rootElement 0 2) (rootElement 0 1) (rootElement 1 2)
    ⟨![4, 2, 0, 6, 1, 3, 5, 7], ![2, 4, 1, 5, 0, 6, 3, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder9 (x : V) :
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (x))) := by
  apply reorder_three ρ (rootElement 1 2) (rootElement 0 2) (rootElement 0 1) (rootElement 1 2) (rootElement 0 1) (rootElement 0 2)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder10 (x : V) :
    difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (x))) =
    difference ρ (rootElement 2 4) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 4) (x))) := by
  apply reorder_three ρ (rootElement 2 4) (rootElement 1 4) (rootElement 1 3) (rootElement 2 4) (rootElement 1 3) (rootElement 1 4)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder11 (x : V) :
    difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (x)) =
    difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (x)) := by
  apply reorder_two ρ (rootElement 0 4) (rootElement 0 3) (rootElement 0 3) (rootElement 0 4)
    ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder12 (x : V) :
    difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 2 4) (difference ρ (rootElement 0 1) (difference ρ (rootElement 0 4) (x))) := by
  apply reorder_three ρ (rootElement 2 4) (rootElement 0 4) (rootElement 0 1) (rootElement 2 4) (rootElement 0 1) (rootElement 0 4)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder13 (x : V) :
    difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (x))) =
    difference ρ (rootElement 0 1) (difference ρ (rootElement 0 4) (difference ρ (rootElement 2 4) (x))) := by
  apply reorder_three ρ (rootElement 2 4) (rootElement 0 4) (rootElement 0 1) (rootElement 0 1) (rootElement 0 4) (rootElement 2 4)
    ⟨![0, 4, 2, 6, 1, 5, 3, 7], ![0, 4, 2, 6, 1, 5, 3, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder14 (x : V) :
    difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (x))) =
    difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (x))) := by
  apply reorder_three ρ (rootElement 2 4) (rootElement 0 4) (rootElement 0 3) (rootElement 2 4) (rootElement 0 3) (rootElement 0 4)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

omit h in
private theorem reorder15 (x : V) :
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (x))) =
    difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (x))) := by
  apply reorder_three ρ (rootElement 1 2) (rootElement 0 4) (rootElement 0 2) (rootElement 1 2) (rootElement 0 2) (rootElement 0 4)
    ⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide +kernel, by decide +kernel⟩
  decide +kernel

private theorem action0 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by decide) 1 2 (by decide)
  decide +kernel

private theorem action1 : difference ρ (rootElement 1 2) (ρ w1 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 2) w1 w0
    [] [] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action2 : difference ρ (rootElement 2 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w0
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action3 : difference ρ (rootElement 2 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w1
    [] (by decide) 1 3 (by decide)
  decide +kernel

private theorem action4 : difference ρ (rootElement 2 3) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 3) w2 w0
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action5 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action6 : difference ρ (rootElement 0 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action7 : difference ρ (rootElement 0 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action8 : difference ρ (rootElement 0 1) (ρ w3 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 1) w3 w1
    [0] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action9 : difference ρ (rootElement 1 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w0
    [] (by decide) 1 3 (by decide)
  decide +kernel

private theorem action10 : difference ρ (rootElement 1 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w1
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action11 : difference ρ (rootElement 1 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by decide) 1 2 (by decide)
  decide +kernel

private theorem action12 : difference ρ (rootElement 1 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w3
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action13 : difference ρ (rootElement 1 3) (ρ w4 v) = ρ w1 v := by
  apply difference_step h (rootElement 1 3) w4 w1
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action14 : difference ρ (rootElement 1 3) (ρ w5 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 3) w5 w2
    [] [] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action15 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action16 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action17 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action18 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action19 : difference ρ (rootElement 2 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w4
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action20 : difference ρ (rootElement 2 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w5
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action21 : difference ρ (rootElement 2 4) (ρ w6 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 4) w6 w0
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action22 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action23 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action24 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action25 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action26 : difference ρ (rootElement 0 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w4
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action27 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action28 : difference ρ (rootElement 0 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w6
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action29 : difference ρ (rootElement 0 3) (ρ w7 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 3) w7 w2
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action30 : difference ρ (rootElement 0 1) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w4
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action31 : difference ρ (rootElement 0 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w5
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action32 : difference ρ (rootElement 0 1) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w6
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action33 : difference ρ (rootElement 0 1) (ρ w7 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 1) w7 w5
    [0] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action34 : difference ρ (rootElement 0 3) (ρ w8 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 3) w8 w3
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action35 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action36 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action37 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action38 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action39 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action40 : difference ρ (rootElement 1 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action41 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by decide) 1 2 (by decide)
  decide +kernel

private theorem action42 : difference ρ (rootElement 1 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w7
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action43 : difference ρ (rootElement 1 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w8
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action44 : difference ρ (rootElement 1 4) (ρ w9 v) = ρ w1 v := by
  apply difference_step h (rootElement 1 4) w9 w1
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action45 : difference ρ (rootElement 1 4) (ρ w10 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 4) w10 w6
    [] [] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action46 : difference ρ (rootElement 1 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w2
    [] (by decide) 1 3 (by decide)
  decide +kernel

private theorem action47 : difference ρ (rootElement 1 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w3
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action48 : difference ρ (rootElement 1 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w5
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action49 : difference ρ (rootElement 1 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w6
    [] (by decide) 1 3 (by decide)
  decide +kernel

private theorem action50 : difference ρ (rootElement 1 2) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w7
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action51 : difference ρ (rootElement 1 2) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w8
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action52 : difference ρ (rootElement 1 3) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w9
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action53 : difference ρ (rootElement 1 2) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w10
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action54 : difference ρ (rootElement 1 2) (ρ w11 v) = ρ w5 v := by
  apply difference_step h (rootElement 1 2) w11 w5
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action55 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action56 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action57 : difference ρ (rootElement 0 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w2
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action58 : difference ρ (rootElement 0 2) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 2) w3 w0
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action59 : difference ρ (rootElement 0 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w4
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action60 : difference ρ (rootElement 0 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action61 : difference ρ (rootElement 0 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w6
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action62 : difference ρ (rootElement 0 2) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w7
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action63 : difference ρ (rootElement 0 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w9
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action64 : difference ρ (rootElement 0 2) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w10
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action65 : difference ρ (rootElement 0 2) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w11
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action66 : difference ρ (rootElement 0 2) (ρ w12 v) = ρ w11 v := by
  apply difference_step h (rootElement 0 2) w12 w11
    [0] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action67 : difference ρ (rootElement 0 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w0
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action68 : difference ρ (rootElement 0 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w1
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action69 : difference ρ (rootElement 0 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action70 : difference ρ (rootElement 0 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w3
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action71 : difference ρ (rootElement 0 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w4
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action72 : difference ρ (rootElement 0 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action73 : difference ρ (rootElement 0 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w6
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action74 : difference ρ (rootElement 0 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w7
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action75 : difference ρ (rootElement 0 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w8
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action76 : difference ρ (rootElement 0 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w9
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action77 : difference ρ (rootElement 0 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w10
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action78 : difference ρ (rootElement 0 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w11
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action79 : difference ρ (rootElement 0 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w12
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action80 : difference ρ (rootElement 0 4) (ρ w13 v) = ρ w6 v := by
  apply difference_step h (rootElement 0 4) w13 w6
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action81 : difference ρ (rootElement 1 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action82 : difference ρ (rootElement 1 2) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w13
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action83 : difference ρ (rootElement 1 2) (ρ w14 v) = ρ w10 v := by
  apply difference_step h (rootElement 1 2) w14 w10
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action84 : difference ρ (rootElement 0 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w9
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action85 : difference ρ (rootElement 0 1) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w10
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action86 : difference ρ (rootElement 0 1) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w11
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action87 : difference ρ (rootElement 0 1) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w12
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action88 : difference ρ (rootElement 0 1) (ρ w13 v) = ρ w10 v := by
  apply difference_step h (rootElement 0 1) w13 w10
    [0] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action89 : difference ρ (rootElement 0 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w10
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action90 : difference ρ (rootElement 0 1) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w14
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action91 : difference ρ (rootElement 2 3) (ρ w15 v) = ρ w8 v := by
  apply difference_step h (rootElement 2 3) w15 w8
    [] [] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action92 : difference ρ (rootElement 1 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w6
    [] (by decide) 1 4 (by decide)
  decide +kernel

private theorem action93 : difference ρ (rootElement 1 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w7
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action94 : difference ρ (rootElement 1 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w8
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action95 : difference ρ (rootElement 1 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w10
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action96 : difference ρ (rootElement 1 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w11
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action97 : difference ρ (rootElement 1 3) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w13
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action98 : difference ρ (rootElement 1 3) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w14
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action99 : difference ρ (rootElement 1 3) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w15
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action100 : difference ρ (rootElement 1 4) (ρ w16 v) = ρ w5 v := by
  apply difference_step h (rootElement 1 4) w16 w5
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action101 : difference ρ (rootElement 0 4) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w15
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action102 : difference ρ (rootElement 0 1) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w16
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action103 : difference ρ (rootElement 0 4) (ρ w17 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 4) w17 w3
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action104 : difference ρ (rootElement 0 2) (ρ w15 v) = ρ w7 v := by
  apply difference_step h (rootElement 0 2) w15 w7
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action105 : difference ρ (rootElement 1 2) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w17
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action106 : difference ρ (rootElement 0 1) (ρ w18 v) = ρ w12 v := by
  apply difference_step h (rootElement 0 1) w18 w12
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action107 : difference ρ (rootElement 0 4) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w14
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action108 : difference ρ (rootElement 0 4) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w16
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action109 : difference ρ (rootElement 0 4) (ρ w18 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w18
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action110 : difference ρ (rootElement 0 4) (ρ w19 v) = ρ w9 v := by
  apply difference_step h (rootElement 0 4) w19 w9
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action111 : difference ρ (rootElement 1 3) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w17
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action112 : difference ρ (rootElement 1 3) (ρ w18 v) = ρ w8 v := by
  apply difference_step h (rootElement 1 3) w18 w8
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action113 : difference ρ (rootElement 1 3) (ρ w19 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w19
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action114 : difference ρ (rootElement 1 3) (ρ w20 v) = ρ w10 v := by
  apply difference_step h (rootElement 1 3) w20 w10
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action115 : difference ρ (rootElement 0 3) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w9
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action116 : difference ρ (rootElement 0 3) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w11
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action117 : difference ρ (rootElement 0 3) (ρ w12 v) = ρ w4 v := by
  apply difference_step h (rootElement 0 3) w12 w4
    [] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action118 : difference ρ (rootElement 0 3) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w13
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action119 : difference ρ (rootElement 0 3) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w14
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action120 : difference ρ (rootElement 0 3) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w16
    [] (by decide) 0 1 (by decide)
  decide +kernel

private theorem action121 : difference ρ (rootElement 0 3) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w17
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action122 : difference ρ (rootElement 0 3) (ρ w19 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w19
    [] (by decide) 2 4 (by decide)
  decide +kernel

private theorem action123 : difference ρ (rootElement 0 3) (ρ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w20
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action124 : difference ρ (rootElement 0 4) (ρ w21 v) = ρ w7 v := by
  apply difference_step h (rootElement 0 4) w21 w7
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action125 : difference ρ (rootElement 0 1) (ρ w19 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w19
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action126 : difference ρ (rootElement 0 1) (ρ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w20
    [] (by decide) 0 3 (by decide)
  decide +kernel

private theorem action127 : difference ρ (rootElement 2 4) (ρ w22 v) = ρ w17 v := by
  apply difference_step h (rootElement 2 4) w22 w17
    [] [] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action128 : difference ρ (rootElement 0 3) (ρ w22 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w22
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action129 : difference ρ (rootElement 0 3) (ρ w23 v) = ρ w13 v := by
  apply difference_step h (rootElement 0 3) w23 w13
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action130 : difference ρ (rootElement 0 2) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w13
    [] (by decide) 2 3 (by decide)
  decide +kernel

private theorem action131 : difference ρ (rootElement 0 2) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w14
    [] (by decide) 0 2 (by decide)
  decide +kernel

private theorem action132 : difference ρ (rootElement 0 2) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w16
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action133 : difference ρ (rootElement 0 2) (ρ w19 v) = ρ w14 v := by
  apply difference_step h (rootElement 0 2) w19 w14
    [0] [0] (by decide) (by decide) 1 (by decide) <;> decide +kernel

private theorem action134 : difference ρ (rootElement 0 2) (ρ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w20
    [] (by decide) 0 4 (by decide)
  decide +kernel

private theorem action135 : difference ρ (rootElement 0 2) (ρ w21 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w21
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action136 : difference ρ (rootElement 0 2) (ρ w22 v) = ρ w13 v := by
  apply difference_step h (rootElement 0 2) w22 w13
    [] [] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private theorem action137 : difference ρ (rootElement 0 2) (ρ w23 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w23
    [] (by decide) 3 4 (by decide)
  decide +kernel

private theorem action138 : difference ρ (rootElement 0 4) (ρ w24 v) = ρ w12 v := by
  apply difference_step h (rootElement 0 4) w24 w12
    [] [3] (by decide) (by decide) 2 (by decide) <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V)
    (v : V) : Fin 25 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v, ρ w11 v, ρ w12 v, ρ w13 v, ρ w14 v, ρ w15 v, ρ w16 v, ρ w17 v, ρ w18 v, ρ w19 v, ρ w20 v, ρ w21 v, ρ w22 v, ρ w23 v, ρ w24 v]
private def extractors (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) :
    Fin 25 → V →ₗ[ZMod 2] V :=
  ![
    LinearMap.id,
    (difference ρ (rootElement 1 2)).comp (LinearMap.id),
    (difference ρ (rootElement 2 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 1 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 1 2)).comp (LinearMap.id))),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 4)).comp (LinearMap.id),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 1 2)).comp (LinearMap.id))),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 0 3)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id))),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 1 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 4)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id))),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 1 3)).comp (LinearMap.id))),
    (difference ρ (rootElement 0 4)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 0 4)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id))),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 0 4)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id))),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 4)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)))]
omit h in

private theorem kills0 (j : Fin 25) (hj : j.val < 0) :
    extractors ρ 0 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj

private theorem kills1 (j : Fin 25) (hj : j.val < 1) :
    extractors ρ 1 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (ρ w0 v) = 0
    simp only [action0 h]

private theorem kills2 (j : Fin 25) (hj : j.val < 2) :
    extractors ρ 2 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (ρ w0 v) = 0
    simp only [action2 h]
  · change difference ρ (rootElement 2 3) (ρ w1 v) = 0
    simp only [action3 h]

private theorem kills3 (j : Fin 25) (hj : j.val < 3) :
    extractors ρ 3 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
    simp only [action5 h]
  · change difference ρ (rootElement 0 1) (ρ w1 v) = 0
    simp only [action6 h]
  · change difference ρ (rootElement 0 1) (ρ w2 v) = 0
    simp only [action7 h]

private theorem kills4 (j : Fin 25) (hj : j.val < 4) :
    extractors ρ 4 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
    simp only [action9 h]
  · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
    simp only [action10 h]
  · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
    simp only [action11 h]
  · change difference ρ (rootElement 1 3) (ρ w3 v) = 0
    simp only [action12 h]

private theorem kills5 (j : Fin 25) (hj : j.val < 5) :
    extractors ρ 5 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w0 v)) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w1 v)) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w2 v)) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w3 v)) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w4 v)) = 0
    simp only [action13 h, action3 h]

private theorem kills6 (j : Fin 25) (hj : j.val < 6) :
    extractors ρ 6 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (ρ w0 v) = 0
    simp only [action15 h]
  · change difference ρ (rootElement 2 4) (ρ w1 v) = 0
    simp only [action16 h]
  · change difference ρ (rootElement 2 4) (ρ w2 v) = 0
    simp only [action17 h]
  · change difference ρ (rootElement 2 4) (ρ w3 v) = 0
    simp only [action18 h]
  · change difference ρ (rootElement 2 4) (ρ w4 v) = 0
    simp only [action19 h]
  · change difference ρ (rootElement 2 4) (ρ w5 v) = 0
    simp only [action20 h]

private theorem kills7 (j : Fin 25) (hj : j.val < 7) :
    extractors ρ 7 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
    simp only [action22 h]
  · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
    simp only [action23 h]
  · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
    simp only [action24 h]
  · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
    simp only [action25 h]
  · change difference ρ (rootElement 0 3) (ρ w4 v) = 0
    simp only [action26 h]
  · change difference ρ (rootElement 0 3) (ρ w5 v) = 0
    simp only [action27 h]
  · change difference ρ (rootElement 0 3) (ρ w6 v) = 0
    simp only [action28 h]

private theorem kills8 (j : Fin 25) (hj : j.val < 8) :
    extractors ρ 8 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
    simp only [action8 h, action23 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
    simp only [action33 h, action27 h]

private theorem kills9 (j : Fin 25) (hj : j.val < 9) :
    extractors ρ 9 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
    simp only [action35 h]
  · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
    simp only [action36 h]
  · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
    simp only [action37 h]
  · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
    simp only [action38 h]
  · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
    simp only [action39 h]
  · change difference ρ (rootElement 1 4) (ρ w5 v) = 0
    simp only [action40 h]
  · change difference ρ (rootElement 1 4) (ρ w6 v) = 0
    simp only [action41 h]
  · change difference ρ (rootElement 1 4) (ρ w7 v) = 0
    simp only [action42 h]
  · change difference ρ (rootElement 1 4) (ρ w8 v) = 0
    simp only [action43 h]

private theorem kills10 (j : Fin 25) (hj : j.val < 10) :
    extractors ρ 10 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
    simp only [action35 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
    simp only [action36 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
    simp only [action37 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
    simp only [action38 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
    simp only [action39 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
    simp only [action40 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
    simp only [action41 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
    simp only [action42 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
    simp only [action43 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
    simp only [action44 h, action16 h]

private theorem kills11 (j : Fin 25) (hj : j.val < 11) :
    extractors ρ 11 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w0 v))) = 0
    simp only [action0 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w1 v))) = 0
    simp only [action1 h, action9 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w2 v))) = 0
    simp only [action46 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w3 v))) = 0
    simp only [action47 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w4 v))) = 0
    rw [reorder1]
    simp only [action13 h, action1 h, action2 h]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w5 v))) = 0
    simp only [action48 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w6 v))) = 0
    simp only [action49 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w7 v))) = 0
    simp only [action50 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w8 v))) = 0
    simp only [action51 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w9 v))) = 0
    rw [reorder1]
    simp only [action52 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w10 v))) = 0
    simp only [action53 h, map_zero]

private theorem kills12 (j : Fin 25) (hj : j.val < 12) :
    extractors ρ 12 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
    simp only [action55 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
    simp only [action56 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
    simp only [action57 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
    simp only [action58 h, action0 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
    simp only [action59 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
    simp only [action60 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
    simp only [action61 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w7 v)) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w8 v)) = 0
    rw [reorder2]
    simp only [action51 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w9 v)) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w10 v)) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w11 v)) = 0
    simp only [action65 h, map_zero]

private theorem kills13 (j : Fin 25) (hj : j.val < 13) :
    extractors ρ 13 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 4) (ρ w0 v) = 0
    simp only [action67 h]
  · change difference ρ (rootElement 0 4) (ρ w1 v) = 0
    simp only [action68 h]
  · change difference ρ (rootElement 0 4) (ρ w2 v) = 0
    simp only [action69 h]
  · change difference ρ (rootElement 0 4) (ρ w3 v) = 0
    simp only [action70 h]
  · change difference ρ (rootElement 0 4) (ρ w4 v) = 0
    simp only [action71 h]
  · change difference ρ (rootElement 0 4) (ρ w5 v) = 0
    simp only [action72 h]
  · change difference ρ (rootElement 0 4) (ρ w6 v) = 0
    simp only [action73 h]
  · change difference ρ (rootElement 0 4) (ρ w7 v) = 0
    simp only [action74 h]
  · change difference ρ (rootElement 0 4) (ρ w8 v) = 0
    simp only [action75 h]
  · change difference ρ (rootElement 0 4) (ρ w9 v) = 0
    simp only [action76 h]
  · change difference ρ (rootElement 0 4) (ρ w10 v) = 0
    simp only [action77 h]
  · change difference ρ (rootElement 0 4) (ρ w11 v) = 0
    simp only [action78 h]
  · change difference ρ (rootElement 0 4) (ρ w12 v) = 0
    simp only [action79 h]

private theorem kills14 (j : Fin 25) (hj : j.val < 14) :
    extractors ρ 14 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w0 v))) = 0
    simp only [action0 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w1 v))) = 0
    simp only [action1 h, action35 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w2 v))) = 0
    simp only [action46 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w3 v))) = 0
    simp only [action47 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w4 v))) = 0
    rw [reorder3]
    simp only [action39 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w5 v))) = 0
    simp only [action48 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w6 v))) = 0
    simp only [action49 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w7 v))) = 0
    simp only [action50 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w8 v))) = 0
    simp only [action51 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w9 v))) = 0
    rw [reorder3]
    simp only [action44 h, action1 h, action15 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w10 v))) = 0
    simp only [action53 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w11 v))) = 0
    simp only [action54 h, action40 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w12 v))) = 0
    rw [reorder3]
    simp only [action81 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w13 v))) = 0
    simp only [action82 h, map_zero]

private theorem kills15 (j : Fin 25) (hj : j.val < 15) :
    extractors ρ 15 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w0 v))) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w1 v))) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w2 v))) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w3 v))) = 0
    simp only [action8 h, action23 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w4 v))) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w5 v))) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w6 v))) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w7 v))) = 0
    simp only [action33 h, action27 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w8 v))) = 0
    rw [reorder4]
    simp only [action34 h, action8 h, action3 h]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w9 v))) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w10 v))) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w11 v))) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w12 v))) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w13 v))) = 0
    simp only [action88 h, action89 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w14 v))) = 0
    simp only [action90 h, map_zero]

private theorem kills16 (j : Fin 25) (hj : j.val < 16) :
    extractors ρ 16 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w0 v)) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w1 v)) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w2 v)) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w3 v)) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w4 v)) = 0
    simp only [action13 h, action36 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w5 v)) = 0
    simp only [action14 h, action37 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w6 v)) = 0
    simp only [action92 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w7 v)) = 0
    simp only [action93 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w8 v)) = 0
    simp only [action94 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w9 v)) = 0
    simp only [action52 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w10 v)) = 0
    simp only [action95 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w11 v)) = 0
    rw [reorder6]
    simp only [action96 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w12 v)) = 0
    rw [reorder6]
    simp only [action81 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w13 v)) = 0
    simp only [action97 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w14 v)) = 0
    simp only [action98 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w15 v)) = 0
    simp only [action99 h, map_zero]

private theorem kills17 (j : Fin 25) (hj : j.val < 17) :
    extractors ρ 17 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
    simp only [action8 h, action68 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
    simp only [action33 h, action72 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w8 v)) = 0
    rw [reorder7]
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w9 v)) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w10 v)) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w11 v)) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w12 v)) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w13 v)) = 0
    simp only [action88 h, action77 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w14 v)) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w15 v)) = 0
    rw [reorder7]
    simp only [action101 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w16 v)) = 0
    simp only [action102 h, map_zero]

private theorem kills18 (j : Fin 25) (hj : j.val < 18) :
    extractors ρ 18 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w0 v))) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w1 v))) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w2 v))) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w3 v))) = 0
    simp only [action8 h, action56 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w4 v))) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w5 v))) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w6 v))) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w7 v))) = 0
    simp only [action33 h, action60 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w8 v))) = 0
    rw [reorder8]
    simp only [action51 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w9 v))) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w10 v))) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w11 v))) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w12 v))) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w13 v))) = 0
    simp only [action88 h, action64 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w14 v))) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w15 v))) = 0
    rw [reorder9]
    simp only [action104 h, action33 h, action48 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w16 v))) = 0
    simp only [action102 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w17 v))) = 0
    rw [reorder8]
    simp only [action105 h, map_zero]

private theorem kills19 (j : Fin 25) (hj : j.val < 19) :
    extractors ρ 19 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    simp only [action67 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    simp only [action68 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    simp only [action69 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    simp only [action70 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    simp only [action71 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    simp only [action72 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    simp only [action73 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    simp only [action74 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    simp only [action76 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    simp only [action77 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    simp only [action78 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    simp only [action79 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    simp only [action80 h, action41 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    simp only [action107 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    simp only [action101 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    simp only [action108 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    simp only [action103 h, action38 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w18 v)) = 0
    simp only [action109 h, map_zero]

private theorem kills20 (j : Fin 25) (hj : j.val < 20) :
    extractors ρ 20 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w0 v))) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w1 v))) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w2 v))) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w3 v))) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w4 v))) = 0
    simp only [action13 h, action36 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w5 v))) = 0
    simp only [action14 h, action37 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w6 v))) = 0
    simp only [action92 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w7 v))) = 0
    simp only [action93 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w8 v))) = 0
    simp only [action94 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w9 v))) = 0
    simp only [action52 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w10 v))) = 0
    simp only [action95 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w11 v))) = 0
    rw [reorder10]
    simp only [action96 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w12 v))) = 0
    rw [reorder10]
    simp only [action81 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w13 v))) = 0
    simp only [action97 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w14 v))) = 0
    simp only [action98 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w15 v))) = 0
    simp only [action99 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w16 v))) = 0
    rw [reorder10]
    simp only [action100 h, action14 h, action17 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w17 v))) = 0
    simp only [action111 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w18 v))) = 0
    simp only [action112 h, action43 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w19 v))) = 0
    simp only [action113 h, map_zero]

private theorem kills21 (j : Fin 25) (hj : j.val < 21) :
    extractors ρ 21 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    simp only [action29 h, action69 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    simp only [action34 h, action70 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    simp only [action115 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    simp only [action89 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    simp only [action116 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w12 v)) = 0
    simp only [action117 h, action71 h]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w13 v)) = 0
    simp only [action118 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w14 v)) = 0
    simp only [action119 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w15 v)) = 0
    rw [reorder11]
    simp only [action101 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w16 v)) = 0
    simp only [action120 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w17 v)) = 0
    simp only [action121 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w18 v)) = 0
    rw [reorder11]
    simp only [action109 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w19 v)) = 0
    simp only [action122 h, map_zero]
  · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w20 v)) = 0
    simp only [action123 h, map_zero]

private theorem kills22 (j : Fin 25) (hj : j.val < 22) :
    extractors ρ 22 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w0 v))) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w1 v))) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w2 v))) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w3 v))) = 0
    simp only [action8 h, action68 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w4 v))) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w5 v))) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w6 v))) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w7 v))) = 0
    simp only [action33 h, action72 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w8 v))) = 0
    rw [reorder12]
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w9 v))) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w10 v))) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w11 v))) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w12 v))) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w13 v))) = 0
    simp only [action88 h, action77 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w14 v))) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w15 v))) = 0
    rw [reorder12]
    simp only [action101 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w16 v))) = 0
    simp only [action102 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w17 v))) = 0
    rw [reorder12]
    simp only [action103 h, action8 h, action16 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w18 v))) = 0
    simp only [action106 h, action79 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w19 v))) = 0
    simp only [action125 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w20 v))) = 0
    simp only [action126 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w21 v))) = 0
    rw [reorder12]
    simp only [action124 h, action33 h, action20 h]

private theorem kills23 (j : Fin 25) (hj : j.val < 23) :
    extractors ρ 23 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w0 v))) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w1 v))) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w2 v))) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w3 v))) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w4 v))) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w5 v))) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w6 v))) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w7 v))) = 0
    simp only [action29 h, action69 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w8 v))) = 0
    simp only [action34 h, action70 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w9 v))) = 0
    simp only [action115 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w10 v))) = 0
    simp only [action89 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w11 v))) = 0
    simp only [action116 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w12 v))) = 0
    simp only [action117 h, action71 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w13 v))) = 0
    simp only [action118 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w14 v))) = 0
    simp only [action119 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w15 v))) = 0
    rw [reorder14]
    simp only [action101 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w16 v))) = 0
    simp only [action120 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w17 v))) = 0
    simp only [action121 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w18 v))) = 0
    rw [reorder14]
    simp only [action109 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w19 v))) = 0
    simp only [action122 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w20 v))) = 0
    simp only [action123 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w21 v))) = 0
    rw [reorder14]
    simp only [action124 h, action29 h, action17 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w22 v))) = 0
    simp only [action128 h, map_zero]

private theorem kills24 (j : Fin 25) (hj : j.val < 24) :
    extractors ρ 24 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w0 v))) = 0
    simp only [action55 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w1 v))) = 0
    simp only [action56 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w2 v))) = 0
    simp only [action57 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w3 v))) = 0
    simp only [action58 h, action67 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w4 v))) = 0
    simp only [action59 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w5 v))) = 0
    simp only [action60 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w6 v))) = 0
    simp only [action61 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w7 v))) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w8 v))) = 0
    rw [reorder15]
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w9 v))) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w10 v))) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w11 v))) = 0
    simp only [action65 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w12 v))) = 0
    simp only [action66 h, action78 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w13 v))) = 0
    simp only [action130 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w14 v))) = 0
    simp only [action131 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w15 v))) = 0
    simp only [action104 h, action74 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w16 v))) = 0
    simp only [action132 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w17 v))) = 0
    rw [reorder15]
    simp only [action103 h, action58 h, action0 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w18 v))) = 0
    rw [reorder15]
    simp only [action109 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w19 v))) = 0
    simp only [action133 h, action107 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w20 v))) = 0
    simp only [action134 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w21 v))) = 0
    simp only [action135 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w22 v))) = 0
    simp only [action136 h, action80 h, action49 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w23 v))) = 0
    simp only [action137 h, map_zero]

private theorem independent (hv : v ≠ 0) :
    LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i
    · exact kills0 j hij
    · exact kills1 h j hij
    · exact kills2 h j hij
    · exact kills3 h j hij
    · exact kills4 h j hij
    · exact kills5 h j hij
    · exact kills6 h j hij
    · exact kills7 h j hij
    · exact kills8 h j hij
    · exact kills9 h j hij
    · exact kills10 h j hij
    · exact kills11 h j hij
    · exact kills12 h j hij
    · exact kills13 h j hij
    · exact kills14 h j hij
    · exact kills15 h j hij
    · exact kills16 h j hij
    · exact kills17 h j hij
    · exact kills18 h j hij
    · exact kills19 h j hij
    · exact kills20 h j hij
    · exact kills21 h j hij
    · exact kills22 h j hij
    · exact kills23 h j hij
    · exact kills24 h j hij
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (ρ w5 v)) ≠ 0
      rw [action14 h, action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (ρ w6 v) ≠ 0
      rw [action21 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w7 v) ≠ 0
      rw [action29 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w8 v)) ≠ 0
      rw [reorder0]
      rw [action34 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w9 v) ≠ 0
      rw [action44 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (ρ w10 v)) ≠ 0
      rw [action45 h, action21 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 3) (difference ρ (rootElement 1 2) (ρ w11 v))) ≠ 0
      rw [action54 h, action14 h, action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w12 v)) ≠ 0
      rw [action66 h, action54 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (ρ w13 v) ≠ 0
      rw [action80 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 2) (ρ w14 v))) ≠ 0
      rw [action83 h, action45 h, action21 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 0 1) (ρ w15 v))) ≠ 0
      rw [reorder5]
      rw [action91 h, action34 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w16 v)) ≠ 0
      rw [reorder6]
      rw [action100 h, action14 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w17 v)) ≠ 0
      rw [reorder7]
      rw [action103 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (difference ρ (rootElement 0 1) (ρ w18 v))) ≠ 0
      rw [action106 h, action66 h, action54 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w19 v)) ≠ 0
      rw [action110 h, action44 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 1 4) (difference ρ (rootElement 1 3) (ρ w20 v))) ≠ 0
      rw [action114 h, action45 h, action21 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w21 v)) ≠ 0
      rw [reorder11]
      rw [action124 h, action29 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 1) (ρ w22 v))) ≠ 0
      rw [reorder13]
      rw [action127 h, action103 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 3) (ρ w23 v))) ≠ 0
      rw [action129 h, action80 h, action21 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (difference ρ (rootElement 0 2) (ρ w24 v))) ≠ 0
      rw [reorder15]
      rw [action138 h, action66 h, action54 h]
      exact translate_ne_zero ρ _ hv

/-- Exact middle-adjacent support forces twenty-five independent dimensions. -/
theorem finrank_ge_twentyFive [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    25 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.MiddlePair
