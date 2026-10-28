module
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Theory.SpecificGroups.GL2.SignedFiveOvergroups.Certificate
public import Mathlib.GroupTheory.Sylow


/-!
# Signed-matrix Sylow images in GL₂(5)

Every proper overgroup of the signed permutation matrices contains the central
scalar 2I. The checked word certificate proves that containment for each
invertible matrix. Orthogonality excludes 2I from the signed subgroup, while
its central cyclic two-group lies in every Sylow two-subgroup. Consequently
an action with this Sylow image has the same image on the whole group.

The source consumer is the residual-normalizer reduction in original 14.6.15,
Aschbacher–Smith, printed p.1034. The matrix certificate is checked separately;
these proofs transport its tuple calculation to the actual general linear group.
-/

@[expose] public section

open Subgroup Matrix
namespace Matrix.GeneralLinearGroup.SignedFive
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F := ZMod 5
abbrev L := GL (Fin 2) F
noncomputable def signedSubgroup : Subgroup L := diagonalSwapSubgroup F (-1)
noncomputable def scalar : L := diagonalPair F (Units.mk0 2 (by decide),Units.mk0 2 (by decide))
private abbrev r : L := diagonalPair F (-1,1)
private abbrev t : L := coordinateSwap F
private abbrev r' : L := diagonalPair F (1,-1)
private def matrix (a : SignedFiveCertificate.Mat) : Matrix (Fin 2) (Fin 2) F :=
  !![a.1,a.2.1;a.2.2.1,a.2.2.2]
private theorem matrix_mul (a b : SignedFiveCertificate.Mat) :
    matrix (SignedFiveCertificate.mul a b) = matrix a * matrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,SignedFiveCertificate.mul,Matrix.mul_apply,Fin.sum_univ_two]
private theorem matrix_neg (a : SignedFiveCertificate.Mat) :
    matrix (SignedFiveCertificate.neg a) = -matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
private theorem matrix_id : matrix SignedFiveCertificate.identity = 1 := by decide
private noncomputable def word (a : L) : ℕ → ℕ → L
  | 0,_ => 1
  | k+1,n => if n=0 then 1 else
      (if n%4=1 then r else if n%4=2 then t else a) * word a k (n/4)
private theorem word_val (a : L) (k n : ℕ) :
    (word a k n).val = matrix (SignedFiveCertificate.eval
      (a.val 0 0,a.val 0 1,a.val 1 0,a.val 1 1) k n) := by
  induction k generalizing n with
  | zero => exact matrix_id.symm
  | succ k ih =>
    by_cases h : n=0
    · simp only [word,SignedFiveCertificate.eval,h,ite_true]
      exact matrix_id.symm
    · simp only [word,SignedFiveCertificate.eval,h,ite_false,matrix_mul,Units.val_mul,ih]
      congr 1
      split_ifs <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [matrix,SignedFiveCertificate.reflection,SignedFiveCertificate.swap,
          r,t,diagonalPair_val,coordinateSwap_val]
private theorem word_mem (H : Subgroup L) (hr : r ∈ H) (ht : t ∈ H)
    (a : L) (ha : a ∈ H) (k n : ℕ) : word a k n ∈ H := by
  induction k generalizing n with
  | zero => exact H.one_mem
  | succ k ih =>
    simp only [word]
    split_ifs <;> first | exact H.one_mem | exact H.mul_mem hr (ih _) |
      exact H.mul_mem ht (ih _) | exact H.mul_mem ha (ih _)
private theorem signed_mem (a : L)
    (h : SignedFiveCertificate.signed (a.val 0 0,a.val 0 1,a.val 1 0,a.val 1 1)) :
    a ∈ signedSubgroup := by
  have hr : r ∈ signedSubgroup := subset_closure (by simp [r])
  have ht : t ∈ signedSubgroup := subset_closure (by simp [t])
  have hr' : r' ∈ signedSubgroup := subset_closure (by simp [r'])
  have hn : (-1 : L) ∈ signedSubgroup := by
    have he : r*r' = -1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [r,r',diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two]
    exact he ▸ signedSubgroup.mul_mem hr hr'
  have hneg {b : L} (hb : b ∈ signedSubgroup) : -b ∈ signedSubgroup := by
    simpa only [neg_one_mul] using signedSubgroup.mul_mem hn hb
  rcases h with h | h | h | h | h | h | h | h
  all_goals
    have hh := congrArg matrix h
    have hm : matrix (a.val 0 0,a.val 0 1,a.val 1 0,a.val 1 1) = a.val := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm] at hh
  · have he : a=1 := Units.ext (hh.trans matrix_id)
    exact he ▸ signedSubgroup.one_mem
  · have he : a=r := Units.ext hh
    exact he ▸ hr
  · have he : a= -1 := Units.ext (by simpa only [matrix_neg,matrix_id,Units.val_neg,Units.val_one] using hh)
    exact he ▸ hn
  · have he : a= -r := Units.ext (by rw [matrix_neg] at hh; exact hh)
    exact he ▸ hneg hr
  · have he : a=t := Units.ext hh
    exact he ▸ ht
  · have he : a=r*t := Units.ext (hh.trans (matrix_mul _ _))
    exact he ▸ signedSubgroup.mul_mem hr ht
  · have he : a= -t := Units.ext (by rw [matrix_neg] at hh; exact hh)
    exact he ▸ hneg ht
  · have he : a= -(r*t) := by
      apply Units.ext
      rw [hh,matrix_neg,matrix_mul]
      rfl
    exact he ▸ hneg (signedSubgroup.mul_mem hr ht)

/-- A proper overgroup of the actual signed matrices contains the central scalar 2I. -/
theorem scalar_mem_of_signed_lt (H : Subgroup L) (h : signedSubgroup < H) : scalar ∈ H := by
  obtain ⟨a,ha,hout⟩ := SetLike.exists_of_lt h
  have hd : a.val 0 0 * a.val 1 1 - a.val 0 1 * a.val 1 0 ≠ 0 := by
    simpa only [Matrix.det_fin_two] using det_ne_zero a
  rcases SignedFiveCertificate.checked (a.val 0 0) (a.val 0 1) (a.val 1 0) (a.val 1 1) hd
    with hs | ⟨n,hn⟩
  · exact (hout (signed_mem a hs)).elim
  have hr : r ∈ H := h.le (subset_closure (by simp [r]))
  have ht : t ∈ H := h.le (subset_closure (by simp [t]))
  have he : word a 15 n = scalar := Units.ext (by rw [word_val,hn]; rfl)
  exact he ▸ word_mem H hr ht a ha 15 n

private theorem scalar_not_mem_signed : scalar ∉ signedSubgroup := by
  intro hs
  have hp : ∀ a ∈ signedSubgroup, a.val.transpose * a.val = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      all_goals
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [diagonalPair_val,coordinateSwap_val,Matrix.mul_apply,Fin.sum_univ_two]
    | one => simp
    | mul a b ha hb ia ib =>
      change (a.val*b.val).transpose * (a.val*b.val) = 1
      rw [Matrix.transpose_mul,←mul_assoc, mul_assoc b.val.transpose, ia]
      simpa using ib
    | inv a ha ih =>
      change a.inv.transpose*a.inv = 1
      calc
        _ = a.inv.transpose*(a.val.transpose*a.val)*a.inv := by rw [ih]; simp
        _ = (a.val*a.inv).transpose*(a.val*a.inv) := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
        _ = 1 := by rw [a.val_inv]; simp
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) (hp scalar hs)
  norm_num [scalar,diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two] at hh
  exact (by decide : (4:F) ≠ 1) hh

private theorem scalar_pow_four : scalar^4 = 1 := by
  change diagonalPair F (Units.mk0 2 (by decide),Units.mk0 2 (by decide)) ^ 4 = 1
  rw [←map_pow]
  have h : (Units.mk0 (2:F) (by decide),Units.mk0 (2:F) (by decide)) ^ 4 = 1 := by decide
  rw [h,map_one]

private theorem scalar_central (a : L) : a*scalar = scalar*a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalar,diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

/-- The signed matrices cannot be Sylow in a proper overgroup in GL₂(5). -/
theorem eq_signed_of_sylow (H : Subgroup L) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = signedSubgroup) : H = signedSubgroup := by
  have hle : signedSubgroup ≤ H := hS ▸ map_subtype_le (S : Subgroup H)
  by_contra hne
  have hc : scalar ∈ H := scalar_mem_of_signed_lt H (lt_of_le_of_ne hle (Ne.symm hne))
  let c : H := ⟨scalar,hc⟩
  have hp : IsPGroup 2 (zpowers c) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext scalar_pow_four)
  have hn : (zpowers c).Normal := by
    have hcent : zpowers c ≤ center H := zpowers_le.mpr
      (mem_center_iff.mpr (fun a => Subtype.ext (scalar_central a)))
    refine ⟨fun n hn g => ?_⟩
    rw [(mem_center_iff.mp (hcent hn)) g,mul_inv_cancel_right]
    exact hn
  have hm : c ∈ S := hp.le_sylow_of_normal S (mem_zpowers c)
  apply scalar_not_mem_signed
  rw [←hS]
  exact mem_map_of_mem H.subtype hm

/-- Any finite-group action whose Sylow image is the signed subgroup has
exactly that image on the whole group. -/
theorem range_eq_signed_of_sylow {D : Type*} [Group D] [Finite D]
    (f : D →* L) (S : Sylow 2 D)
    (hS : (S : Subgroup D).map f = signedSubgroup) : f.range = signedSubgroup := by
  let S' := S.mapSurjective f.rangeRestrict_surjective
  apply eq_signed_of_sylow f.range S'
  rw [Sylow.coe_mapSurjective,Subgroup.map_map]
  exact hS
end Matrix.GeneralLinearGroup.SignedFive
