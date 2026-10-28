module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.FinCases

/-!
# Elementary eights in odd-characteristic SL₄ and PSL₄

Two determinant-one diagonal involutions commute projectively with the double
transposition (01)(23). Their eight projective products are distinct: an
off-diagonal entry detects the permutation, and three diagonal entries remove
the scalar ambiguity and recover both sign parameters. For the covering SL₄,
replace the double transposition by scalar minus one; its independent parameter
is detected after projecting the other two signs to PSL₄.

These give the degree-four witnesses for the linear-family two-rank sieve in
Aschbacher–Smith A.2.12, printed p.36. Both embeddings are constructed on the
actual matrix groups; no rank monotonicity through a two-kernel is used.
-/

open Matrix
open scoped MatrixGroups
namespace Matrix.PSL4.OddTwoRank
variable (F : Type*) [Field F]

private def diagA : SL(4,F) :=
  ⟨diagonal ![-1,-1,1,1], by simp [det_diagonal, Fin.prod_univ_succ]⟩
private def diagC : SL(4,F) :=
  ⟨diagonal ![-1,1,-1,1], by simp [det_diagonal, Fin.prod_univ_succ]⟩
private def swapD : SL(4,F) :=
  ⟨!![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0], by
    simp [det_succ_row_zero, Fin.sum_univ_succ]
    rfl⟩

private theorem diagA_sq : diagA F ^ 2 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, pow_two]
  change (diagonal ![-1,-1,1,1] : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1,-1,1,1] = 1
  rw [diagonal_mul_diagonal, diagonal_eq_one]
  funext i
  fin_cases i <;> simp
private theorem diagC_sq : diagC F ^ 2 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, pow_two]
  change (diagonal ![-1,1,-1,1] : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1,1,-1,1] = 1
  rw [diagonal_mul_diagonal, diagonal_eq_one]
  funext i
  fin_cases i <;> simp
private theorem swapD_sq : swapD F ^ 2 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, pow_two]
  change (swapD F).val * (swapD F).val = (1 : Matrix (Fin 4) (Fin 4) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapD, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem diag_commute : Commute (diagA F) (diagC F) := by
  apply Subtype.ext
  change (diagonal ![-1,-1,1,1] : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1,1,-1,1] =
    diagonal ![-1,1,-1,1] * diagonal ![-1,-1,1,1]
  simp only [diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _
private theorem diagA_swapD_commute : Commute (diagA F) (swapD F) := by
  apply Subtype.ext
  change (diagA F).val * (swapD F).val = (swapD F).val * (diagA F).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagA, swapD, Matrix.mul_apply, Fin.sum_univ_succ]

private def imageA : PSL(4,F) := QuotientGroup.mk' _ (diagA F)
private def imageC : PSL(4,F) := QuotientGroup.mk' _ (diagC F)
private def imageD : PSL(4,F) := QuotientGroup.mk' _ (swapD F)

private theorem imageC_imageD_commute : Commute (imageC F) (imageD F) := by
  change QuotientGroup.mk' _ (diagC F) * QuotientGroup.mk' _ (swapD F) =
    QuotientGroup.mk' _ (swapD F) * QuotientGroup.mk' _ (diagC F)
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq.mpr
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1, by simp [pow_succ], ?_⟩
  have hc : (diagC F)⁻¹ = diagC F := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using diagC_sq F)
  have hd : (swapD F)⁻¹ = swapD F := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using swapD_sq F)
  simp only [mul_inv_rev, hc, hd, SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagC, swapD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]


private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))

private theorem imageA_sq : imageA F ^ 2 = 1 := by
  simpa only [imageA, map_pow, map_one] using congrArg (QuotientGroup.mk' (Subgroup.center SL(4,F)))
    (diagA_sq F)
private theorem imageC_sq : imageC F ^ 2 = 1 := by
  simpa only [imageC, map_pow, map_one] using congrArg (QuotientGroup.mk' (Subgroup.center SL(4,F)))
    (diagC_sq F)
private theorem imageD_sq : imageD F ^ 2 = 1 := by
  simpa only [imageD, map_pow, map_one] using congrArg (QuotientGroup.mk' (Subgroup.center SL(4,F)))
    (swapD_sq F)

private def embedding : E →* PSL(4,F) :=
  tripleHom (imageA F) (imageC F) (imageD F) (imageA_sq F) (imageC_sq F) (imageD_sq F)
    ((diag_commute F).map (QuotientGroup.mk' _))
    ((diagA_swapD_commute F).map (QuotientGroup.mk' _)) (imageC_imageD_commute F)

private def raw (a b c : C2) : SL(4,F) :=
  (if a = 1 then 1 else diagA F) * (if b = 1 then 1 else diagC F) *
    (if c = 1 then 1 else swapD F)

private theorem raw_coe (a b c : C2) :
    (raw F a b c).val =
      (if a = 1 then (1 : Matrix (Fin 4) (Fin 4) F) else (diagA F).val) *
      (if b = 1 then 1 else (diagC F).val) * (if c = 1 then 1 else (swapD F).val) := by
  unfold raw
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  split_ifs <;> rfl

private theorem embedding_raw (a b c : C2) :
    embedding F ((a,b),c) = QuotientGroup.mk' _ (raw F a b c) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk, raw, map_mul]
  by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> by_cases hc : c = 1 <;>
    simp [ha,hb,hc,imageA,imageC,imageD]

private theorem embedding_injective (hF : (2 : F) ≠ 0) :
    Function.Injective (embedding F) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨a,b⟩,c⟩ hh
  rw [embedding_raw] at hh
  have hz : raw F a b c ∈ Subgroup.center SL(4,F) := (QuotientGroup.eq_one_iff _).mp hh
  obtain ⟨s, _, hs⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  rw [raw_coe] at hs
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hs
  have hc : c = 1 := by
    by_contra hc
    by_cases ha : a = 1 <;> by_cases hb : b = 1 <;>
      simp [ha,hb,hc,diagA,diagC,swapD,
        Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] at h01
  have h3 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 3 3) hs
  have hs1 : s = 1 := by
    by_cases ha : a = 1 <;> by_cases hb : b = 1 <;>
      simpa [ha,hb,hc,diagA,diagC,
        Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] using h3
  subst s
  have hneg : (-1 : F) ≠ 1 := by
    intro hn
    apply hF
    simpa only [neg_add_cancel,one_add_one_eq_two] using congrArg (fun x : F => x+1) hn.symm
  have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 1) hs
  have ha : a = 1 := by
    by_contra ha
    by_cases hb : b = 1 <;>
      simp [ha,hb,hc,diagA,diagC,
        Matrix.mul_apply,Matrix.one_apply,eq_comm (a := (1:F)),hneg] at h1
  have h2 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 2) hs
  have hb : b = 1 := by
    by_contra hb
    simp [ha,hb,hc,diagC,
      Matrix.mul_apply,Matrix.one_apply,eq_comm (a := (1:F)),hneg] at h2
  exact Prod.ext (Prod.ext ha hb) hc


private def scalarZ : SL(4,F) :=
  ⟨diagonal ![-1,-1,-1,-1], by simp [det_diagonal,Fin.prod_univ_succ]⟩
private theorem scalarZ_sq : scalarZ F ^ 2 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow,SpecialLinearGroup.coe_one,pow_two]
  change (diagonal ![-1,-1,-1,-1] : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1,-1,-1,-1] = 1
  rw [diagonal_mul_diagonal,diagonal_eq_one]
  funext i
  fin_cases i <;> simp
private theorem scalarZ_central : scalarZ F ∈ Subgroup.center SL(4,F) := by
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1,by simp [pow_succ],?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarZ,Matrix.scalar_apply]
private theorem scalarZ_ne_one (hF : (2:F) ≠ 0) : scalarZ F ≠ 1 := by
  intro h
  have he := congrArg (fun g : SL(4,F) => g.val 0 0) h
  have hn : (-1:F) = 1 := by simpa [scalarZ] using he
  apply hF
  simpa only [neg_add_cancel,one_add_one_eq_two] using congrArg (fun x:F => x+1) hn.symm

private def liftEmbedding : E →* SL(4,F) :=
  tripleHom (diagA F) (diagC F) (scalarZ F) (diagA_sq F) (diagC_sq F) (scalarZ_sq F)
    (diag_commute F)
    ((Subgroup.mem_center_iff.mp (scalarZ_central F) (diagA F)))
    ((Subgroup.mem_center_iff.mp (scalarZ_central F) (diagC F)))

private theorem project_liftEmbedding (a b c : C2) :
    QuotientGroup.mk' _ (liftEmbedding F ((a,b),c)) = embedding F ((a,b),1) := by
  have hz : QuotientGroup.mk' (Subgroup.center SL(4,F)) (scalarZ F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (scalarZ_central F)
  simp only [liftEmbedding,embedding,tripleHom,MonoidHom.noncommCoprod_apply,binaryHom,
    MonoidHom.coe_mk,OneHom.coe_mk,map_mul]
  by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> by_cases hc : c = 1 <;>
    simp [ha,hb,hc,hz,imageA,imageC]

private theorem liftEmbedding_injective (hF : (2:F) ≠ 0) :
    Function.Injective (liftEmbedding F) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨a,b⟩,c⟩ h
  have hp := congrArg (QuotientGroup.mk' (Subgroup.center SL(4,F))) h
  rw [project_liftEmbedding,map_one] at hp
  have hab : ((a,b), (1:C2)) = 1 :=
    embedding_injective F hF (hp.trans (embedding F).map_one.symm)
  have ha : a = 1 := congrArg (fun x : E => x.1.1) hab
  have hb : b = 1 := congrArg (fun x : E => x.1.2) hab
  have hc : c = 1 := by
    by_contra hc
    have hz : scalarZ F = 1 := by
      simpa [liftEmbedding,tripleHom,MonoidHom.noncommCoprod_apply,binaryHom,ha,hb,hc] using h
    exact scalarZ_ne_one F hF hz
  exact Prod.ext (Prod.ext ha hb) hc

private theorem square : ∀ a : E, a ^ 2 = 1 := by decide +kernel
private theorem card : Nat.card E = 2 ^ 3 := by simp [E,C2]

public theorem three_le_projectiveRank [Finite F] (hF : (2:F) ≠ 0) :
    3 ≤ primeRank 2 PSL(4,F) :=
  primeRank_ge_of_elementary_embedding square card (embedding F) (embedding_injective F hF)

public theorem three_le_specialRank [Finite F] (hF : (2:F) ≠ 0) :
    3 ≤ primeRank 2 SL(4,F) :=
  primeRank_ge_of_elementary_embedding square card (liftEmbedding F) (liftEmbedding_injective F hF)
end Matrix.PSL4.OddTwoRank
