module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyCommutators
import Mathlib.Data.Matrix.Basis

/-!
# Arbitrary-ring G2 root-curve swap relations

This module turns the finite sparse-polynomial calculation in
`G2ChevalleyCommutators` into the actual unit equality
`rootCurveSwapRelation r s a b` over every commutative ring, for distinct
non-opposite roots.  Thus the integral correction table is available to the
explicit Bruhat collection argument, including in characteristics two and
three.

The proof interprets a sparse bivariate checker matrix as a matrix over the
given ring.  Normalization, addition, and multiplication preserve this
interpretation.  A coordinate-valid, duplicate-free integral entry list is
then identified with the scalar extension of the production
`matrixOfEntries`; applying this once to each of the three divided-power
tables shows that checker root curves specialize to the production
`rootCurve` matrices.  The interpretation is propagated through the folded
correction word, and the public all-roots Boolean certificate supplies the
required sparse equality.

All coefficients and parameters remain integral polynomials.  The argument
uses only the explicit representation, carrier/root-curve construction, and
commutator table developed in the preceding G2 modules.  Its source is the
standard integral Chevalley commutator calculation encoded by that table; no
classification, root-exhaustiveness, division, or characteristic restriction
is used here.
-/

open scoped BigOperators Matrix

namespace Theory.AlgebraicGroup.G2Chevalley

private def evalBiPoly {R : Type*} [CommRing R] (a b : R) (p : BiPoly) : R :=
  p.foldr (fun e acc => (e.2.2 : R) * a ^ e.1 * b ^ e.2.1 + acc) 0

private lemma evalBiPoly_insertTerm {R : Type*} [CommRing R] (a b : R)
    (i j : ℕ) (c : ℤ) (p : BiPoly) :
    evalBiPoly a b (insertTerm i j c p) =
      (c : R) * a ^ i * b ^ j + evalBiPoly a b p := by
  induction p with
  | nil =>
      simp only [insertTerm]
      by_cases hc : c = 0
      · subst c
        simp [evalBiPoly]
      · rw [if_neg hc]
        simp [evalBiPoly]
  | cons e es ih =>
      rcases e with ⟨i', j', c'⟩
      simp only [insertTerm]
      by_cases hc : c = 0
      · rw [if_pos hc]
        subst c
        simp [evalBiPoly]
      · rw [if_neg hc]
        by_cases hij : i = i' ∧ j = j'
        · rw [if_pos hij]
          rcases hij with ⟨rfl, rfl⟩
          by_cases hsum : c + c' = 0
          · rw [if_pos hsum]
            simp only [evalBiPoly, List.foldr_cons]
            have hcast : (c : R) + (c' : R) = 0 := by
              rw [← Int.cast_add, hsum, Int.cast_zero]
            calc
              evalBiPoly a b es = ((c : R) + (c' : R)) *
                  (a ^ i * b ^ j) + evalBiPoly a b es := by rw [hcast]; simp
              _ = (c : R) * a ^ i * b ^ j +
                  ((c' : R) * a ^ i * b ^ j + evalBiPoly a b es) := by ring
          · rw [if_neg hsum]
            simp only [evalBiPoly, List.foldr_cons]
            push_cast
            ring
        · rw [if_neg hij]
          by_cases hless : monomialLess i j i' j' = true
          · rw [if_pos hless]
            simp [evalBiPoly]
          · rw [if_neg hless]
            simp only [evalBiPoly, List.foldr_cons]
            change (c' : R) * a ^ i' * b ^ j' +
                evalBiPoly a b (insertTerm i j c es) =
              (c : R) * a ^ i * b ^ j +
                ((c' : R) * a ^ i' * b ^ j' + evalBiPoly a b es)
            rw [ih]
            ring

private lemma evalBiPoly_normalize {R : Type*} [CommRing R] (a b : R)
    (p : BiPoly) :
    evalBiPoly a b (normalizeBiPoly p) = evalBiPoly a b p := by
  induction p with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      change evalBiPoly a b (insertTerm i j c (normalizeBiPoly es)) = _
      rw [evalBiPoly_insertTerm, ih]
      rfl

private lemma evalBiPoly_append {R : Type*} [CommRing R] (a b : R)
    (p q : BiPoly) :
    evalBiPoly a b (p ++ q) = evalBiPoly a b p + evalBiPoly a b q := by
  induction p with
  | nil => simp [evalBiPoly]
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      simp only [List.cons_append, evalBiPoly, List.foldr_cons]
      change (c : R) * a ^ i * b ^ j + evalBiPoly a b (es ++ q) =
        ((c : R) * a ^ i * b ^ j + evalBiPoly a b es) + evalBiPoly a b q
      rw [ih]
      ring

private lemma evalBiPoly_add {R : Type*} [CommRing R] (a b : R)
    (p q : BiPoly) :
    evalBiPoly a b (biAdd p q) = evalBiPoly a b p + evalBiPoly a b q := by
  rw [biAdd, evalBiPoly_normalize, evalBiPoly_append]

private lemma evalBiPoly_map_mul {R : Type*} [CommRing R] (a b : R)
    (i j : ℕ) (c : ℤ) (q : BiPoly) :
    evalBiPoly a b
        (q.map fun f => (i + f.1, j + f.2.1, c * f.2.2)) =
      ((c : R) * a ^ i * b ^ j) * evalBiPoly a b q := by
  induction q with
  | nil => simp [evalBiPoly]
  | cons f fs ih =>
      rcases f with ⟨i', j', c'⟩
      simp only [List.map_cons, evalBiPoly, List.foldr_cons]
      change ((c * c' : ℤ) : R) * a ^ (i + i') * b ^ (j + j') +
          evalBiPoly a b
            (fs.map fun f => (i + f.1, j + f.2.1, c * f.2.2)) =
        ((c : R) * a ^ i * b ^ j) *
          ((c' : R) * a ^ i' * b ^ j' + evalBiPoly a b fs)
      rw [ih]
      simp only [pow_add]
      push_cast
      ring

private lemma evalBiPoly_flatMap_mul {R : Type*} [CommRing R] (a b : R)
    (p q : BiPoly) :
    evalBiPoly a b
        (p.flatMap fun e =>
          q.map fun f => (e.1 + f.1, e.2.1 + f.2.1, e.2.2 * f.2.2)) =
      evalBiPoly a b p * evalBiPoly a b q := by
  induction p with
  | nil => simp [evalBiPoly]
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      change evalBiPoly a b
          ((q.map fun f => (i + f.1, j + f.2.1, c * f.2.2)) ++
            (es.flatMap fun e =>
              q.map fun f => (e.1 + f.1, e.2.1 + f.2.1, e.2.2 * f.2.2))) = _
      rw [evalBiPoly_append, evalBiPoly_map_mul, ih]
      simp only [evalBiPoly, List.foldr_cons]
      ring

private lemma evalBiPoly_mul {R : Type*} [CommRing R] (a b : R)
    (p q : BiPoly) :
    evalBiPoly a b (biMul p q) = evalBiPoly a b p * evalBiPoly a b q := by
  rw [biMul, evalBiPoly_normalize, evalBiPoly_flatMap_mul]

private lemma evalBiPoly_scaleInt {R : Type*} [CommRing R] (a b : R)
    (c : ℤ) (p : BiPoly) :
    evalBiPoly a b (biScaleInt c p) = (c : R) * evalBiPoly a b p := by
  rw [biScaleInt, evalBiPoly_normalize]
  induction p with
  | nil => simp [evalBiPoly]
  | cons e es ih =>
      rcases e with ⟨i, j, c'⟩
      simp only [List.map_cons, evalBiPoly, List.foldr_cons]
      change ((c * c' : ℤ) : R) * a ^ i * b ^ j +
          evalBiPoly a b (es.map fun e => (e.1, e.2.1, c * e.2.2)) =
        (c : R) * ((c' : R) * a ^ i * b ^ j + evalBiPoly a b es)
      rw [ih]
      push_cast
      ring

private lemma evalBiPoly_zero {R : Type*} [CommRing R] (a b : R) :
    evalBiPoly a b biZero = 0 := rfl

private lemma evalBiPoly_one {R : Type*} [CommRing R] (a b : R) :
    evalBiPoly a b biOne = 1 := by
  simp [evalBiPoly, biOne]

private lemma evalBiPoly_eq_of_biEq_eq_true {R : Type*} [CommRing R]
    (a b : R) {p q : BiPoly} (h : biEq p q = true) :
    evalBiPoly a b p = evalBiPoly a b q := by
  have hnormalize : normalizeBiPoly p = normalizeBiPoly q := by
    exact of_decide_eq_true h
  rw [← evalBiPoly_normalize a b p, hnormalize, evalBiPoly_normalize]

private def evalSparseTerm {R : Type*} [CommRing R] (a b : R)
    (e : ℕ × ℕ × BiPoly) : Matrix Basis Basis R :=
  if hi : e.1 < 14 then
    if hj : e.2.1 < 14 then
      Matrix.single ⟨e.1, hi⟩ ⟨e.2.1, hj⟩ (evalBiPoly a b e.2.2)
    else 0
  else 0

private def evalSparseBiMatrix {R : Type*} [CommRing R] (a b : R)
    (A : SparseBiMatrix) : Matrix Basis Basis R :=
  (A.map (evalSparseTerm a b)).sum

private lemma evalSparseTerm_normalize {R : Type*} [CommRing R] (a b : R)
    (i j : ℕ) (p : BiPoly) :
    evalSparseTerm a b (i, j, normalizeBiPoly p) =
      evalSparseTerm a b (i, j, p) := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalBiPoly_normalize]
  all_goals rfl

private lemma evalSparseTerm_zero_of_biEq_eq_true
    {R : Type*} [CommRing R] (a b : R) (i j : ℕ) {p : BiPoly}
    (h : biEq p biZero = true) :
    evalSparseTerm a b (i, j, p) = 0 := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalBiPoly_eq_of_biEq_eq_true a b h, evalBiPoly_zero]
    exact Matrix.single_zero _ _
  all_goals rfl

private lemma evalSparseTerm_biAdd {R : Type*} [CommRing R] (a b : R)
    (i j : ℕ) (p q : BiPoly) :
    evalSparseTerm a b (i, j, biAdd p q) =
      evalSparseTerm a b (i, j, p) + evalSparseTerm a b (i, j, q) := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalBiPoly_add, Matrix.single_add]
  all_goals simp

private lemma evalSparseBiMatrix_cons {R : Type*} [CommRing R] (a b : R)
    (e : ℕ × ℕ × BiPoly) (A : SparseBiMatrix) :
    evalSparseBiMatrix a b (e :: A) =
      evalSparseTerm a b e + evalSparseBiMatrix a b A := rfl

private lemma evalSparseBiMatrix_insert {R : Type*} [CommRing R] (a b : R)
    (i j : ℕ) (p : BiPoly) (A : SparseBiMatrix) :
    evalSparseBiMatrix a b (insertSparseBiMatrixEntry i j p A) =
      evalSparseTerm a b (i, j, p) + evalSparseBiMatrix a b A := by
  induction A generalizing p with
  | nil =>
      simp only [insertSparseBiMatrixEntry]
      by_cases hp : biEq p biZero = true
      · rw [if_pos hp, evalSparseTerm_zero_of_biEq_eq_true a b i j hp]
        simp [evalSparseBiMatrix]
      · rw [if_neg hp]
        simp [evalSparseBiMatrix, evalSparseTerm_normalize]
  | cons e es ih =>
      rcases e with ⟨i', j', q⟩
      simp only [insertSparseBiMatrixEntry]
      let p' := normalizeBiPoly p
      by_cases hp : biEq p' biZero = true
      · rw [if_pos hp]
        rw [← evalSparseTerm_normalize a b i j p,
          evalSparseTerm_zero_of_biEq_eq_true a b i j hp]
        simp
      · rw [if_neg hp]
        by_cases hij : i = i' ∧ j = j'
        · rw [if_pos hij]
          rcases hij with ⟨rfl, rfl⟩
          let psum := biAdd p' q
          by_cases hsum : biEq psum biZero = true
          · rw [if_pos hsum]
            have hzero := evalSparseTerm_zero_of_biEq_eq_true
              a b i j hsum
            rw [evalSparseTerm_biAdd, evalSparseTerm_normalize] at hzero
            rw [evalSparseBiMatrix_cons]
            calc
              evalSparseBiMatrix a b es = 0 + evalSparseBiMatrix a b es := by simp
              _ = (evalSparseTerm a b (i, j, p) +
                    evalSparseTerm a b (i, j, q)) +
                  evalSparseBiMatrix a b es := by rw [hzero]
              _ = evalSparseTerm a b (i, j, p) +
                  (evalSparseTerm a b (i, j, q) +
                    evalSparseBiMatrix a b es) := by ac_rfl
          · rw [if_neg hsum]
            rw [evalSparseBiMatrix_cons, evalSparseBiMatrix_cons,
              evalSparseTerm_biAdd, evalSparseTerm_normalize]
            ac_rfl
        · rw [if_neg hij]
          by_cases hless : sparseEntryLess i j i' j' = true
          · rw [if_pos hless]
            simp [evalSparseBiMatrix_cons, evalSparseTerm_normalize]
          · rw [if_neg hless]
            rw [evalSparseBiMatrix_cons, evalSparseBiMatrix_cons,
              ih (p := normalizeBiPoly p), evalSparseTerm_normalize]
            ac_rfl

private lemma evalSparseBiMatrix_normalize {R : Type*} [CommRing R]
    (a b : R) (A : SparseBiMatrix) :
    evalSparseBiMatrix a b (normalizeSparseBiMatrix A) =
      evalSparseBiMatrix a b A := by
  induction A with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨i, j, p⟩
      change evalSparseBiMatrix a b
          (insertSparseBiMatrixEntry i j p (normalizeSparseBiMatrix es)) = _
      rw [evalSparseBiMatrix_insert, ih]
      rfl

private lemma evalSparseBiMatrix_eq_of_sparseBiMatrixEq_eq_true
    {R : Type*} [CommRing R] (a b : R) {A B : SparseBiMatrix}
    (h : sparseBiMatrixEq A B = true) :
    evalSparseBiMatrix a b A = evalSparseBiMatrix a b B := by
  have hnormalize : normalizeSparseBiMatrix A = normalizeSparseBiMatrix B := by
    exact of_decide_eq_true h
  rw [← evalSparseBiMatrix_normalize a b A, hnormalize,
    evalSparseBiMatrix_normalize]

private lemma evalSparseBiMatrix_append {R : Type*} [CommRing R]
    (a b : R) (A B : SparseBiMatrix) :
    evalSparseBiMatrix a b (A ++ B) =
      evalSparseBiMatrix a b A + evalSparseBiMatrix a b B := by
  induction A with
  | nil => simp [evalSparseBiMatrix]
  | cons e es ih =>
      rw [List.cons_append, evalSparseBiMatrix_cons, evalSparseBiMatrix_cons, ih]
      ac_rfl

private lemma evalSparseBiMatrix_add {R : Type*} [CommRing R]
    (a b : R) (A B : SparseBiMatrix) :
    evalSparseBiMatrix a b (sparseBiMatrixAdd A B) =
      evalSparseBiMatrix a b A + evalSparseBiMatrix a b B := by
  rw [sparseBiMatrixAdd, evalSparseBiMatrix_normalize,
    evalSparseBiMatrix_append]

private lemma evalSparseBiMatrix_one {R : Type*} [CommRing R] (a b : R) :
    evalSparseBiMatrix a b sparseBiMatrixOne = 1 := by
  have hterm (i : Basis) :
      evalSparseTerm a b (i.val, i.val, biOne) = Matrix.single i i 1 := by
    simp [evalSparseTerm, i.isLt, evalBiPoly_one]
  have hmap : sparseBiMatrixOne.map (evalSparseTerm a b) =
      allBasis.map (fun i => Matrix.single i i 1) := by
    simp only [sparseBiMatrixOne, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    exact hterm i
  rw [evalSparseBiMatrix, hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [allBasis]

private def SparseBiMatrixValid (A : SparseBiMatrix) : Prop :=
  ∀ e ∈ A, e.1 < 14 ∧ e.2.1 < 14

private lemma sparseBiMatrixValid_insert (i j : ℕ) (p : BiPoly)
    (A : SparseBiMatrix) (hi : i < 14) (hj : j < 14)
    (hA : SparseBiMatrixValid A) :
    SparseBiMatrixValid (insertSparseBiMatrixEntry i j p A) := by
  induction A generalizing p with
  | nil =>
      simp only [insertSparseBiMatrixEntry]
      split_ifs
      · intro e he
        simp at he
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst e
        exact ⟨hi, hj⟩
  | cons e es ih =>
      rcases e with ⟨i', j', q⟩
      have he : i' < 14 ∧ j' < 14 := hA (i', j', q) (by simp)
      have hes : SparseBiMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      simp only [insertSparseBiMatrixEntry]
      let p' := normalizeBiPoly p
      by_cases hp : biEq p' biZero = true
      · rw [if_pos hp]
        exact hA
      · rw [if_neg hp]
        by_cases hcoord : i = i' ∧ j = j'
        · rw [if_pos hcoord]
          let psum := biAdd p' q
          by_cases hsum : biEq psum biZero = true
          · rw [if_pos hsum]
            exact hes
          · rw [if_neg hsum]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact ⟨hi, hj⟩
            · exact hes f hf
        · rw [if_neg hcoord]
          by_cases hless : sparseEntryLess i j i' j' = true
          · rw [if_pos hless]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact ⟨hi, hj⟩
            · exact hA f (by simpa only [List.mem_cons] using hf)
          · rw [if_neg hless]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact he
            · exact ih (p := p') hes f hf

private lemma sparseBiMatrixValid_normalize (A : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) :
    SparseBiMatrixValid (normalizeSparseBiMatrix A) := by
  induction A with
  | nil => simp [SparseBiMatrixValid, normalizeSparseBiMatrix]
  | cons e es ih =>
      rcases e with ⟨i, j, p⟩
      have he : i < 14 ∧ j < 14 := hA (i, j, p) (by simp)
      have hes : SparseBiMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      exact sparseBiMatrixValid_insert i j p (normalizeSparseBiMatrix es)
        he.1 he.2 (ih hes)

private lemma sparseBiMatrixValid_add (A B : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) (hB : SparseBiMatrixValid B) :
    SparseBiMatrixValid (sparseBiMatrixAdd A B) := by
  apply sparseBiMatrixValid_normalize
  intro e he
  rw [List.mem_append] at he
  exact he.elim (hA e) (hB e)

private lemma sparseBiMatrixValid_one : SparseBiMatrixValid sparseBiMatrixOne := by
  intro e he
  simp only [sparseBiMatrixOne, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i.isLt, i.isLt⟩

private lemma evalSparseTerm_mul {R : Type*} [CommRing R] (a b : R)
    (e f : ℕ × ℕ × BiPoly)
    (he : e.1 < 14 ∧ e.2.1 < 14) (hf : f.1 < 14 ∧ f.2.1 < 14) :
    evalSparseTerm a b e * evalSparseTerm a b f =
      if e.2.1 = f.1 then
        evalSparseTerm a b (e.1, f.2.1, biMul e.2.2 f.2.2)
      else 0 := by
  rcases e with ⟨i, j, p⟩
  rcases f with ⟨j', k, q⟩
  simp only at he hf
  simp only [evalSparseTerm, he.1, he.2, hf.1, hf.2,
    dif_pos, evalBiPoly_mul]
  by_cases hj : j = j'
  · subst j'
    rw [if_pos rfl, Matrix.single_mul_single_same]
  · rw [if_neg hj, Matrix.single_mul_single_of_ne]
    intro hfin
    exact hj (Fin.ext_iff.mp hfin)

private lemma evalSparseBiMatrix_filterMap_mul {R : Type*} [CommRing R]
    (a b : R) (e : ℕ × ℕ × BiPoly) (B : SparseBiMatrix)
    (he : e.1 < 14 ∧ e.2.1 < 14) (hB : SparseBiMatrixValid B) :
    evalSparseBiMatrix a b
        (B.filterMap fun f =>
          if e.2.1 = f.1 then
            some (e.1, f.2.1, biMul e.2.2 f.2.2)
          else none) =
      evalSparseTerm a b e * evalSparseBiMatrix a b B := by
  induction B with
  | nil => simp [evalSparseBiMatrix]
  | cons f fs ih =>
      have hf := hB f (by simp)
      have hfs : SparseBiMatrixValid fs := by
        intro g hg
        exact hB g (by simp [hg])
      simp only [List.filterMap_cons]
      split_ifs with hmatch
      · rw [evalSparseBiMatrix_cons, evalSparseBiMatrix_cons,
          ih hfs, mul_add, evalSparseTerm_mul a b e f he hf, if_pos hmatch]
      · rw [evalSparseBiMatrix_cons, ih hfs, mul_add,
          evalSparseTerm_mul a b e f he hf, if_neg hmatch, zero_add]

private lemma evalSparseBiMatrix_flatMap_mul {R : Type*} [CommRing R]
    (a b : R) (A B : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) (hB : SparseBiMatrixValid B) :
    evalSparseBiMatrix a b
        (A.flatMap fun e =>
          B.filterMap fun f =>
            if e.2.1 = f.1 then
              some (e.1, f.2.1, biMul e.2.2 f.2.2)
            else none) =
      evalSparseBiMatrix a b A * evalSparseBiMatrix a b B := by
  induction A with
  | nil => simp [evalSparseBiMatrix]
  | cons e es ih =>
      have he := hA e (by simp)
      have hes : SparseBiMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      rw [List.flatMap_cons, evalSparseBiMatrix_append,
        evalSparseBiMatrix_filterMap_mul a b e B he hB, ih hes,
        evalSparseBiMatrix_cons, add_mul]

private lemma evalSparseBiMatrix_mul {R : Type*} [CommRing R]
    (a b : R) (A B : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) (hB : SparseBiMatrixValid B) :
    evalSparseBiMatrix a b (sparseBiMatrixMul A B) =
      evalSparseBiMatrix a b A * evalSparseBiMatrix a b B := by
  rw [sparseBiMatrixMul, evalSparseBiMatrix_normalize,
    evalSparseBiMatrix_flatMap_mul a b A B hA hB]

private lemma sparseBiMatrixValid_mul (A B : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) (hB : SparseBiMatrixValid B) :
    SparseBiMatrixValid (sparseBiMatrixMul A B) := by
  apply sparseBiMatrixValid_normalize
  intro e he
  simp only [List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨x, hxA, f, hfB, hif⟩ := he
  split at hif
  · simp only [Option.some.injEq] at hif
    subst e
    exact ⟨(hA x hxA).1, (hB f hfB).2⟩
  · contradiction

private def IntegralEntriesValid (entries : List (ℕ × ℕ × ℤ)) : Prop :=
  ∀ e ∈ entries, e.1 < 14 ∧ e.2.1 < 14

private def IntegralEntryCoordinatesNodup
    (entries : List (ℕ × ℕ × ℤ)) : Prop :=
  (entries.map fun e => (e.1, e.2.1)).Nodup

private def specializeIntegralEntry {R : Type*} [CommRing R]
    (e : ℕ × ℕ × ℤ) : Matrix Basis Basis R :=
  if hi : e.1 < 14 then
    if hj : e.2.1 < 14 then
      Matrix.single ⟨e.1, hi⟩ ⟨e.2.1, hj⟩ (e.2.2 : R)
    else 0
  else 0

private lemma evalSparseTerm_scaleInt {R : Type*} [CommRing R]
    (a b : R) (p : BiPoly) (e : ℕ × ℕ × ℤ) :
    evalSparseTerm a b (e.1, e.2.1, biScaleInt e.2.2 p) =
      evalBiPoly a b p • specializeIntegralEntry (R := R) e := by
  rcases e with ⟨i, j, c⟩
  simp only [evalSparseTerm, specializeIntegralEntry]
  split_ifs
  · rw [evalBiPoly_scaleInt]
    ext row col
    simp [Matrix.single_apply, mul_comm]
  all_goals simp

private lemma evalSparseBiMatrix_scaleEntries {R : Type*} [CommRing R]
    (a b : R) (p : BiPoly) (entries : List (ℕ × ℕ × ℤ)) :
    evalSparseBiMatrix a b (sparseBiMatrixScaleEntries p entries) =
      evalBiPoly a b p •
        (entries.map (specializeIntegralEntry (R := R))).sum := by
  rw [sparseBiMatrixScaleEntries, evalSparseBiMatrix_normalize]
  induction entries with
  | nil => simp [evalSparseBiMatrix]
  | cons e es ih =>
      rw [List.map_cons, evalSparseBiMatrix_cons, evalSparseTerm_scaleInt,
        ih, List.map_cons, List.sum_cons, smul_add]

private lemma sparseBiMatrixValid_scaleEntries (p : BiPoly)
    (entries : List (ℕ × ℕ × ℤ)) (hentries : IntegralEntriesValid entries) :
    SparseBiMatrixValid (sparseBiMatrixScaleEntries p entries) := by
  apply sparseBiMatrixValid_normalize
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact hentries f hf

private lemma matrixOfEntries_apply_eq_zero_of_not_mem
    (entries : List (ℕ × ℕ × ℤ)) (row col : Basis)
    (hnot : (row.val, col.val) ∉ entries.map fun e => (e.1, e.2.1)) :
    matrixOfEntries entries row col = 0 := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      have hcoord : ¬(row.val = i ∧ col.val = j) := by
        intro h
        exact hnot (by simp [h])
      have htail : (row.val, col.val) ∉ es.map fun e => (e.1, e.2.1) := by
        intro h
        exact hnot (by simp [h])
      change (if row.val = i ∧ col.val = j then c
        else matrixOfEntries es row col) = 0
      rw [if_neg hcoord, ih htail]

private lemma specialize_matrixOfEntries_eq_sum {R : Type*} [CommRing R]
    (entries : List (ℕ × ℕ × ℤ))
    (hvalid : IntegralEntriesValid entries)
    (hnodup : IntegralEntryCoordinatesNodup entries) :
    specialize (R := R) (matrixOfEntries entries) =
      (entries.map (specializeIntegralEntry (R := R))).sum := by
  induction entries with
  | nil =>
      ext row col
      simp [specialize, matrixOfEntries]
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      have he : i < 14 ∧ j < 14 := hvalid (i, j, c) (by simp)
      have hvalidTail : IntegralEntriesValid es := by
        intro f hf
        exact hvalid f (by simp [hf])
      have hnodup' := List.nodup_cons.mp hnodup
      have hnodupTail : IntegralEntryCoordinatesNodup es := hnodup'.2
      have hnot : (i, j) ∉ es.map fun f => (f.1, f.2.1) := hnodup'.1
      rw [List.map_cons, List.sum_cons, ← ih hvalidTail hnodupTail]
      ext row col
      by_cases hcoord : row.val = i ∧ col.val = j
      · have hrow : row = ⟨i, he.1⟩ := Fin.ext hcoord.1
        have hcol : col = ⟨j, he.2⟩ := Fin.ext hcoord.2
        subst row
        subst col
        have hzero := matrixOfEntries_apply_eq_zero_of_not_mem es
          ⟨i, he.1⟩ ⟨j, he.2⟩ hnot
        change ((if i = i ∧ j = j then c
            else matrixOfEntries es ⟨i, he.1⟩ ⟨j, he.2⟩ : ℤ) : R) =
          specializeIntegralEntry (R := R) (i, j, c) ⟨i, he.1⟩ ⟨j, he.2⟩ +
            ((matrixOfEntries es ⟨i, he.1⟩ ⟨j, he.2⟩ : ℤ) : R)
        rw [if_pos ⟨rfl, rfl⟩, hzero]
        have hentry : specializeIntegralEntry (R := R) (i, j, c) =
            Matrix.single ⟨i, he.1⟩ ⟨j, he.2⟩ (c : R) := by
          simp [specializeIntegralEntry, he.1, he.2]
        rw [hentry]
        simp
      · have hsingle : specializeIntegralEntry (R := R) (i, j, c) row col = 0 := by
          simp only [specializeIntegralEntry, he.1, he.2, dif_pos]
          by_cases hrow : (⟨i, he.1⟩ : Basis) = row
          · have hrowVal : row.val = i := (Fin.ext_iff.mp hrow).symm
            have hcol : (⟨j, he.2⟩ : Basis) ≠ col := by
              intro hcol
              exact hcoord ⟨hrowVal, (Fin.ext_iff.mp hcol).symm⟩
            simp [hrow, hcol]
          · simp [hrow]
        simp only [Matrix.add_apply, hsingle, zero_add, specialize,
          Matrix.map_apply]
        change ((if row.val = i ∧ col.val = j then c
          else matrixOfEntries es row col : ℤ) : R) = _
        rw [if_neg hcoord]
        rfl

private lemma checkerRootOperatorEntries_eq (r : Root) :
    checkerRootOperatorEntries r = rootOperatorEntries r := by
  fin_cases r <;> rfl

private lemma checkerRootDividedPowerTwoEntries_eq (r : Root) :
    checkerRootDividedPowerTwoEntries r = rootDividedPowerTwoEntries r := by
  fin_cases r <;> rfl

private lemma checkerRootDividedPowerThreeEntries_eq (r : Root) :
    checkerRootDividedPowerThreeEntries r = rootDividedPowerThreeEntries r := by
  fin_cases r <;> rfl

private lemma checkerRootOperatorEntries_valid (r : Root) :
    IntegralEntriesValid (checkerRootOperatorEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, checkerRootOperatorEntries]

private lemma checkerRootDividedPowerTwoEntries_valid (r : Root) :
    IntegralEntriesValid (checkerRootDividedPowerTwoEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, checkerRootDividedPowerTwoEntries]

private lemma checkerRootDividedPowerThreeEntries_valid (r : Root) :
    IntegralEntriesValid (checkerRootDividedPowerThreeEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, checkerRootDividedPowerThreeEntries]

private lemma checkerRootOperatorEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (checkerRootOperatorEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup, checkerRootOperatorEntries]

private lemma checkerRootDividedPowerTwoEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (checkerRootDividedPowerTwoEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup,
      checkerRootDividedPowerTwoEntries]

private lemma checkerRootDividedPowerThreeEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (checkerRootDividedPowerThreeEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup,
      checkerRootDividedPowerThreeEntries]

private lemma evalSparseBiMatrix_scaleRootOperator {R : Type*} [CommRing R]
    (a b : R) (p : BiPoly) (r : Root) :
    evalSparseBiMatrix a b
        (sparseBiMatrixScaleEntries p (checkerRootOperatorEntries r)) =
      evalBiPoly a b p • specialize (R := R) (rootDividedPower r 1) := by
  rw [evalSparseBiMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (checkerRootOperatorEntries r)
      (checkerRootOperatorEntries_valid r)
      (checkerRootOperatorEntries_nodup r),
    checkerRootOperatorEntries_eq]
  rfl

private lemma evalSparseBiMatrix_scaleRootDividedPowerTwo
    {R : Type*} [CommRing R] (a b : R) (p : BiPoly) (r : Root) :
    evalSparseBiMatrix a b
        (sparseBiMatrixScaleEntries p
          (checkerRootDividedPowerTwoEntries r)) =
      evalBiPoly a b p • specialize (R := R) (rootDividedPower r 2) := by
  rw [evalSparseBiMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (checkerRootDividedPowerTwoEntries r)
      (checkerRootDividedPowerTwoEntries_valid r)
      (checkerRootDividedPowerTwoEntries_nodup r),
    checkerRootDividedPowerTwoEntries_eq]
  rfl

private lemma evalSparseBiMatrix_scaleRootDividedPowerThree
    {R : Type*} [CommRing R] (a b : R) (p : BiPoly) (r : Root) :
    evalSparseBiMatrix a b
        (sparseBiMatrixScaleEntries p
          (checkerRootDividedPowerThreeEntries r)) =
      evalBiPoly a b p • specialize (R := R) (rootDividedPower r 3) := by
  rw [evalSparseBiMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (checkerRootDividedPowerThreeEntries r)
      (checkerRootDividedPowerThreeEntries_valid r)
      (checkerRootDividedPowerThreeEntries_nodup r),
    checkerRootDividedPowerThreeEntries_eq]
  rfl

private lemma sparseBiMatrixValid_rootCurvePolySparse (r : Root) (p : BiPoly) :
    SparseBiMatrixValid (rootCurvePolySparse r p) := by
  apply sparseBiMatrixValid_add
  · apply sparseBiMatrixValid_add
    · apply sparseBiMatrixValid_add sparseBiMatrixOne
        (sparseBiMatrixScaleEntries p (checkerRootOperatorEntries r))
        sparseBiMatrixValid_one
      exact sparseBiMatrixValid_scaleEntries p _
        (checkerRootOperatorEntries_valid r)
    · exact sparseBiMatrixValid_scaleEntries (biMul p p) _
        (checkerRootDividedPowerTwoEntries_valid r)
  · exact sparseBiMatrixValid_scaleEntries (biMul (biMul p p) p) _
      (checkerRootDividedPowerThreeEntries_valid r)

private lemma evalSparseBiMatrix_rootCurvePolySparse {R : Type*} [CommRing R]
    (a b : R) (r : Root) (p : BiPoly) :
    evalSparseBiMatrix a b (rootCurvePolySparse r p) =
      rootCurve r (evalBiPoly a b p) := by
  simp only [rootCurvePolySparse]
  rw [evalSparseBiMatrix_add, evalSparseBiMatrix_add,
    evalSparseBiMatrix_add, evalSparseBiMatrix_one,
    evalSparseBiMatrix_scaleRootOperator,
    evalSparseBiMatrix_scaleRootDividedPowerTwo,
    evalSparseBiMatrix_scaleRootDividedPowerThree]
  simp_rw [evalBiPoly_mul]
  simp [rootCurve, pow_succ]

private lemma evalBiPoly_monomial {R : Type*} [CommRing R]
    (a b : R) (c : ℤ) (i j : ℕ) :
    evalBiPoly a b (biMonomial c i j) =
      (c : R) * a ^ i * b ^ j := by
  by_cases hc : c = 0
  · subst c
    simp [biMonomial, evalBiPoly]
  · simp [biMonomial, evalBiPoly, hc]

private lemma sparseBiMatrixValid_rootCurveWordFold
    (terms : List RootCurveCommutatorTerm) (A : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) :
    SparseBiMatrixValid
      (terms.foldl
        (fun acc q =>
          sparseBiMatrixMul acc
            (rootCurvePolySparse q.root
              (biMonomial q.coeff q.leftPower q.rightPower))) A) := by
  induction terms generalizing A with
  | nil => exact hA
  | cons q qs ih =>
      apply ih
      exact sparseBiMatrixValid_mul A _ hA
        (sparseBiMatrixValid_rootCurvePolySparse q.root _)

private lemma sparseBiMatrixValid_rootCurveCommutatorWord (r s : Root) :
    SparseBiMatrixValid (rootCurveCommutatorWordSparse r s) := by
  exact sparseBiMatrixValid_rootCurveWordFold
    (rootCurveCommutatorTerms r s) sparseBiMatrixOne
    sparseBiMatrixValid_one

private lemma evalSparseBiMatrix_rootCurveWordFold
    {R : Type*} [CommRing R] (a b : R)
    (terms : List RootCurveCommutatorTerm) (A : SparseBiMatrix)
    (hA : SparseBiMatrixValid A) :
    evalSparseBiMatrix a b
        (terms.foldl
          (fun acc q =>
            sparseBiMatrixMul acc
              (rootCurvePolySparse q.root
                (biMonomial q.coeff q.leftPower q.rightPower))) A) =
      evalSparseBiMatrix a b A *
        (terms.map fun q =>
          rootCurve q.root
            (rootCurveTermParameter a b q)).prod := by
  induction terms generalizing A with
  | nil => simp
  | cons q qs ih =>
      have hq := sparseBiMatrixValid_rootCurvePolySparse q.root
        (biMonomial q.coeff q.leftPower q.rightPower)
      rw [List.foldl_cons, ih _ (sparseBiMatrixValid_mul A _ hA hq),
        evalSparseBiMatrix_mul a b A _ hA hq,
        evalSparseBiMatrix_rootCurvePolySparse,
        evalBiPoly_monomial]
      simp only [rootCurveTermParameter, List.map_cons, List.prod_cons]
      simp [mul_assoc]

private lemma evalSparseBiMatrix_rootCurveCommutatorWord
    {R : Type*} [CommRing R] (a b : R) (r s : Root) :
    evalSparseBiMatrix a b (rootCurveCommutatorWordSparse r s) =
      ((rootCurveCommutatorTerms r s).map fun q =>
        rootCurve q.root (rootCurveTermParameter a b q)).prod := by
  rw [rootCurveCommutatorWordSparse,
    evalSparseBiMatrix_rootCurveWordFold a b _ sparseBiMatrixOne
      sparseBiMatrixValid_one,
    evalSparseBiMatrix_one, one_mul]

private lemma sparseBiMatrixValid_rootCurveCommutatorLeft (r s : Root) :
    SparseBiMatrixValid (rootCurveCommutatorLeftSparse r s) := by
  exact sparseBiMatrixValid_mul _ _
    (sparseBiMatrixValid_rootCurvePolySparse r (biMonomial 1 1 0))
    (sparseBiMatrixValid_rootCurvePolySparse s (biMonomial 1 0 1))

private lemma sparseBiMatrixValid_rootCurveCommutatorRight (r s : Root) :
    SparseBiMatrixValid (rootCurveCommutatorRightSparse r s) := by
  exact sparseBiMatrixValid_mul _ _
    (sparseBiMatrixValid_mul _ _
      (sparseBiMatrixValid_rootCurvePolySparse s (biMonomial 1 0 1))
      (sparseBiMatrixValid_rootCurvePolySparse r (biMonomial 1 1 0)))
    (sparseBiMatrixValid_rootCurveCommutatorWord r s)

private lemma evalSparseBiMatrix_rootCurveCommutatorLeft
    {R : Type*} [CommRing R] (a b : R) (r s : Root) :
    evalSparseBiMatrix a b (rootCurveCommutatorLeftSparse r s) =
      rootCurve r a * rootCurve s b := by
  rw [rootCurveCommutatorLeftSparse,
    evalSparseBiMatrix_mul a b _ _
      (sparseBiMatrixValid_rootCurvePolySparse r (biMonomial 1 1 0))
      (sparseBiMatrixValid_rootCurvePolySparse s (biMonomial 1 0 1)),
    evalSparseBiMatrix_rootCurvePolySparse,
    evalSparseBiMatrix_rootCurvePolySparse,
    evalBiPoly_monomial, evalBiPoly_monomial]
  simp

private lemma evalSparseBiMatrix_rootCurveCommutatorRight
    {R : Type*} [CommRing R] (a b : R) (r s : Root) :
    evalSparseBiMatrix a b (rootCurveCommutatorRightSparse r s) =
      rootCurve s b * rootCurve r a *
        ((rootCurveCommutatorTerms r s).map fun q =>
          rootCurve q.root (rootCurveTermParameter a b q)).prod := by
  rw [rootCurveCommutatorRightSparse,
    evalSparseBiMatrix_mul a b _ _
      (sparseBiMatrixValid_mul _ _
        (sparseBiMatrixValid_rootCurvePolySparse s (biMonomial 1 0 1))
        (sparseBiMatrixValid_rootCurvePolySparse r (biMonomial 1 1 0)))
      (sparseBiMatrixValid_rootCurveCommutatorWord r s),
    evalSparseBiMatrix_mul a b _ _
      (sparseBiMatrixValid_rootCurvePolySparse s (biMonomial 1 0 1))
      (sparseBiMatrixValid_rootCurvePolySparse r (biMonomial 1 1 0)),
    evalSparseBiMatrix_rootCurvePolySparse,
    evalSparseBiMatrix_rootCurvePolySparse,
    evalSparseBiMatrix_rootCurveCommutatorWord,
    evalBiPoly_monomial, evalBiPoly_monomial]
  simp

private lemma rootCurve_matrix_swap_of_pair_checked
    {R : Type*} [CommRing R] (r s : Root) (a b : R)
    (hchecked : rootCurveCommutatorPairChecked r s = true) :
    rootCurve r a * rootCurve s b =
      rootCurve s b * rootCurve r a *
        ((rootCurveCommutatorTerms r s).map fun q =>
          rootCurve q.root (rootCurveTermParameter a b q)).prod := by
  have hmatrix := evalSparseBiMatrix_eq_of_sparseBiMatrixEq_eq_true
    a b hchecked
  rw [evalSparseBiMatrix_rootCurveCommutatorLeft,
    evalSparseBiMatrix_rootCurveCommutatorRight] at hmatrix
  exact hmatrix

private lemma root_mem_allRoots (r : Root) : r ∈ allRoots := by
  fin_cases r <;> simp [allRoots]

private lemma checkerRootNeg_eq_neg (r : Root) : checkerRootNeg r = -r := by
  fin_cases r <;> rfl

private lemma rootCurveCommutatorPairChecked_of_ne_of_ne_neg
    (r s : Root) (hne : r ≠ s) (hneg : s ≠ -r) :
    rootCurveCommutatorPairChecked r s = true := by
  have htable : allRoots.all rootCurveCommutatorRowValid = true :=
    rootCurve_commutator_table_checked
  have hrow : rootCurveCommutatorRowValid r = true :=
    List.all_eq_true.mp htable r (root_mem_allRoots r)
  have hrow' : allRoots.all (fun s =>
      rootCurvePairIsRankOneOrSame r s ||
        rootCurveCommutatorPairChecked r s) = true := hrow
  have hpair :
      (rootCurvePairIsRankOneOrSame r s ||
        rootCurveCommutatorPairChecked r s) = true :=
    List.all_eq_true.mp hrow' s (root_mem_allRoots s)
  rcases Bool.or_eq_true_iff.mp hpair with hrank | hchecked
  · have hrs : r = s ∨ s = checkerRootNeg r := by
      exact of_decide_eq_true hrank
    exact hrs.elim (fun h => (hne h).elim) (fun h =>
      (hneg (h.trans (checkerRootNeg_eq_neg r))).elim)
  · exact hchecked

private lemma rootCurveCorrectionWord_val {R : Type*} [CommRing R]
    (r s : Root) (a b : R) :
    (rootCurveCorrectionWord r s a b).val =
      ((rootCurveCommutatorTerms r s).map fun q =>
        rootCurve q.root (rootCurveTermParameter a b q)).prod := by
  change (((rootCurveCommutatorTerms r s).map
      (fun q => rootCurveUnit q.root
        (rootCurveTermParameter a b q))).prod).val = _
  generalize rootCurveCommutatorTerms r s = terms
  induction terms with
  | nil => rfl
  | cons q qs ih =>
      change rootCurve q.root (rootCurveTermParameter a b q) *
          ((qs.map fun q =>
            rootCurveUnit q.root (rootCurveTermParameter a b q)).prod).val =
        rootCurve q.root (rootCurveTermParameter a b q) *
          (qs.map fun q =>
            rootCurve q.root (rootCurveTermParameter a b q)).prod
      rw [ih]

public theorem rootCurve_swap_relation {R : Type*} [CommRing R]
    (r s : Root) (a b : R) (hne : r ≠ s) (hneg : s ≠ -r) :
    rootCurveSwapRelation r s a b := by
  have hmatrix := rootCurve_matrix_swap_of_pair_checked r s a b
    (rootCurveCommutatorPairChecked_of_ne_of_ne_neg r s hne hneg)
  apply Units.ext
  change rootCurve r a * rootCurve s b =
    rootCurve s b * rootCurve r a * (rootCurveCorrectionWord r s a b).val
  rw [rootCurveCorrectionWord_val]
  exact hmatrix

end Theory.AlgebraicGroup.G2Chevalley
