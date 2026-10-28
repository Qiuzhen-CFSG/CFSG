module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Reduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Simultaneous root placement in the ternary Gram isometry group

An involution preserving the Gram matrix consisting of a symplectic plane and
one nonsingular line has matrix `!![a,b,0; c,a,0; 0,0,1]`. For a commuting family,
if every lower-left entry vanishes, the family already consists of upper root
elements. Otherwise the fixed line of a member with `c ≠ 0` gives the explicit
Gram isometry with plane block `!![0,c⁻¹; c,a+1]`. Commutation then forces every
conjugated lower-left entry to vanish. This works over every characteristic-two
field, without cardinality or field-degree restrictions.

The consumer is `GraphCentralizer.root_placement`, which supplies the actual
matrix involutions constructed from normalized adjoint actors.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section

open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement
open Matrix
variable {F : Type*} [Field F] [CharP F 2]

private lemma sq_one' (a : F) (ha : a ^ 2 = 1) : a = 1 := by
  rcases sq_eq_one_iff.mp ha with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

private lemma involution_block (M : Mat (F := F)) (hM : M * M = 1)
    (hJ : M * gram F * M.transpose = gram F) :
    ∃ a b c : F, M = !![a,b,0; c,a,0; 0,0,1] ∧ a ^ 2 + b * c = 1 := by
  have hd (i : Fin 3) : M i 2 ^ 2 = gram F i i := by
    have hh := congrArg (fun X : Mat (F := F) => X i i) hJ
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_three, mul_comm, pow_two,
      CharTwo.add_self_eq_zero] using hh
  have h02 : M 0 2 = 0 := sq_eq_zero_iff.mp (hd 0)
  have h12 : M 1 2 = 0 := sq_eq_zero_iff.mp (hd 1)
  have h22 : M 2 2 = 1 := sq_one' _ (hd 2)
  have hMT : M * gram F = gram F * M.transpose := by
    have hh := congrArg (fun X => X * M.transpose) hJ
    simpa only [Matrix.mul_assoc, ← Matrix.transpose_mul, hM,
      Matrix.transpose_one, Matrix.mul_one] using hh
  have he (i j : Fin 3) := congrArg (fun X : Mat (F := F) => X i j) hMT
  have h20 : M 2 0 = 0 := by
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_three, h12] using he 2 1
  have h21 : M 2 1 = 0 := by
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_three, h02] using he 2 0
  have h11 : M 1 1 = M 0 0 := by
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_three] using he 1 0
  refine ⟨M 0 0, M 0 1, M 1 0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h22, h11]
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, h02, pow_two] using
      congrArg (fun X : Mat (F := F) => X 0 0) hM

private lemma upper_of_involution_isometry (M : Mat (F := F)) (hM : M * M = 1)
    (hJ : M * gram F * M.transpose = gram F) (h10 : M 1 0 = 0) :
    ∃ a : F, M = unipotent F a := by
  obtain ⟨a,b,c,h,hac⟩ := involution_block M hM hJ
  have hc : c = 0 := by simpa [h] using h10
  have ha : a = 1 := sq_one' a (by simpa [hc] using hac)
  exact ⟨b, by simpa [ha, hc, unipotent] using h⟩

omit [CharP F 2] in
private lemma conjugate_isometry (C s : GL (Fin 3) F)
    (hC : C.val * gram F * C.val.transpose = gram F)
    (hs : s.val * gram F * s.val.transpose = gram F) :
    (C * s * C⁻¹).val * gram F * (C * s * C⁻¹).val.transpose = gram F := by
  have hCi : (C⁻¹).val * gram F * (C⁻¹).val.transpose = gram F := by
    calc
      _ = (C⁻¹).val * (C.val * gram F * C.val.transpose) * (C⁻¹).val.transpose := by
        rw [hC]
      _ = ((C⁻¹).val * C.val) * gram F *
          (C.val.transpose * (C⁻¹).val.transpose) := by simp only [Matrix.mul_assoc]
      _ = gram F := by
        rw [← Matrix.transpose_mul, C.inv_mul, Matrix.transpose_one,
          Matrix.one_mul, Matrix.mul_one]

  change (C.val * s.val * (C⁻¹).val) * gram F *
    (C.val * s.val * (C⁻¹).val).transpose = gram F
  simp only [Matrix.transpose_mul]
  calc
    _ = C.val * s.val * ((C⁻¹).val * gram F * (C⁻¹).val.transpose) *
        s.val.transpose * C.val.transpose := by simp only [Matrix.mul_assoc]
    _ = C.val * (s.val * gram F * s.val.transpose) * C.val.transpose := by
      rw [hCi]; simp only [Matrix.mul_assoc]
    _ = gram F := by rw [hs, hC]

omit [CharP F 2] in
private lemma conjugate_square (C s : GL (Fin 3) F) (hs : s ^ 2 = 1) :
    (C * s * C⁻¹) ^ 2 = 1 := by
  rw [conj_pow, hs]
  simp

/-- Commuting involutions in the literal ternary graph centralizer lie in one
upper root group after a Gram-preserving change of basis. -/
theorem isometry_root_placement {ι : Type*} (s : ι → GL (Fin 3) F)
    (hs : ∀ i, s i ^ 2 = 1)
    (hJ : ∀ i, (s i).val * gram F * (s i).val.transpose = gram F)
    (hc : ∀ i j, Commute (s i) (s j)) :
    ∃ C : GL (Fin 3) F, C.val * gram F * C.val.transpose = gram F ∧
      ∀ i, ∃ a : F, (C * s i * C⁻¹).val = unipotent F a := by
  classical
  have hsq (i : ι) : (s i).val * (s i).val = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val (hs i)
  by_cases hall : ∀ i, (s i).val 1 0 = 0
  · refine ⟨1, by simp, fun i => ?_⟩
    simpa using upper_of_involution_isometry (s i).val (hsq i) (hJ i) (hall i)
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  obtain ⟨a,b,c,hm,hab⟩ := involution_block (s i).val (hsq i) (hJ i)
  have hc0 : c ≠ 0 := by simpa [hm] using hi
  let D : Mat (F := F) := !![0,c⁻¹,0; c,a+1,0; 0,0,1]
  let E : Mat (F := F) := !![a+1,c⁻¹,0; c,0,0; 0,0,1]
  have hDE : D * E = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [D, E, Matrix.mul_apply, Fin.sum_univ_three, hc0, mul_comm,
        CharTwo.add_self_eq_zero]
  have hED : E * D = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [D, E, Matrix.mul_apply, Fin.sum_univ_three, hc0, mul_comm,
        CharTwo.add_self_eq_zero]
  let C : GL (Fin 3) F := ⟨D, E, hDE, hED⟩
  have hC : C.val * gram F * C.val.transpose = gram F := by
    change D * gram F * D.transpose = gram F
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [D, gram, Matrix.mul_apply, Fin.sum_univ_three, hc0,
        mul_comm, CharTwo.add_self_eq_zero]
  refine ⟨C, hC, fun j => ?_⟩
  have hq : (C * s j * C⁻¹).val * (C * s j * C⁻¹).val = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using
      congrArg Units.val (conjugate_square C (s j) (hs j))
  apply upper_of_involution_isometry _ hq (conjugate_isometry C (s j) hC (hJ j))
  obtain ⟨x,y,z,hn,hxyz⟩ := involution_block (s j).val (hsq j) (hJ j)
  have hbc : b * z = y * c := by
    have he := congrArg (fun M : GL (Fin 3) F => M.val 0 0) (hc i j).eq
    simpa [Units.val_mul, hm, hn, Matrix.mul_apply, Fin.sum_univ_three,
      mul_comm] using he
  have hab' : (a+1)^2 = b*c := by
    calc
      (a+1)^2 = a^2 + 1 := by rw [CharTwo.add_sq, one_pow]
      _ = a^2 + (a^2 + b*c) := by rw [hab]
      _ = b*c := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

  change (D * (s j).val * E) 1 0 = 0
  rw [hn]
  simp only [D, E, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

  calc
    _ = c ^ 2 * y + (a+1)^2 * z := by ring_nf; simp [CharTwo.two_eq_zero]
    _ = c * (y*c + b*z) := by rw [hab']; ring
    _ = 0 := by rw [hbc, CharTwo.add_self_eq_zero, mul_zero]

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement
