module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Model
import Mathlib.Tactic.FinCases

/-!
# The literal third local subgroup has at least 2160 elements

Two lists of actual words give 36 distinct images of point zero, and 60
words fixing zero with distinct images of point two. Their products are
2160 distinct elements of the literal subgroup. The discovery is untrusted;
all word evaluations and distinctness assertions are checked by the kernel.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates OrderCertificate Theory.GroupTheory

/-- The literal third local subgroup in the fixed ATLAS marking. -/
def thirdLocalModel : Subgroup Model := closure ({modelGenerator 4,modelGenerator 5} : Set Model)
private def pairGenerator (b : Bool) : Model := if b then modelGenerator 5 else modelGenerator 4
private def fastChain (r : Fin 6156) (s : Fin 510) (t : Fin 16) : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (L0RepWord r) * (L1Rep s * L2Rep t)
private def pairPermutation (b : Bool) : Equiv.Perm (Fin 6156) :=
  if b then fastChain 1197 319 15 else fastChain 5489 314 10
private theorem pairPermutation_eq (b : Bool) : embedding (pairGenerator b) = pairPermutation b := by
  cases b <;> change _ = evalWord fastL0Gen _ * _ <;> rw [fastL0Gen_eq] <;> rfl
private theorem embedding_eval (w : Word Bool) :
    embedding (eval pairGenerator w) = eval pairPermutation w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    congr 1
    cases a with
    | mk i b => cases b <;> simp only [Bool.false_eq_true,↓reduceIte,map_inv,pairPermutation_eq]

private def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i,h⟩ else true)
private theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt,decide_eq_true_eq] using hi

private def baseWord : Fin 36 → Word Bool
  | 0 => []
  | 1 => [(false, true)]
  | 2 => [(true, true)]
  | 3 => [(false, true), (false, true)]
  | 4 => [(true, true), (false, true)]
  | 5 => [(false, true), (true, true)]
  | 6 => [(true, true), (true, true)]
  | 7 => [(false, true), (false, true), (false, true)]
  | 8 => [(true, true), (false, true), (false, true)]
  | 9 => [(false, true), (true, true), (false, true)]
  | 10 => [(true, true), (true, true), (false, true)]
  | 11 => [(true, true), (false, true), (true, true)]
  | 12 => [(false, true), (true, true), (true, true)]
  | 13 => [(false, true), (false, true), (false, true), (false, true)]
  | 14 => [(true, true), (false, true), (false, true), (false, true)]
  | 15 => [(false, true), (true, true), (false, true), (false, true)]
  | 16 => [(true, true), (true, true), (false, true), (false, true)]
  | 17 => [(false, true), (false, true), (true, true), (false, true)]
  | 18 => [(true, true), (false, true), (true, true), (false, true)]
  | 19 => [(true, true), (true, true), (true, true), (false, true)]
  | 20 => [(true, true), (true, true), (false, true), (true, true)]
  | 21 => [(true, true), (false, true), (true, true), (true, true)]
  | 22 => [(true, true), (false, true), (false, true), (false, true), (false, true)]
  | 23 => [(false, true), (true, true), (false, true), (false, true), (false, true)]
  | 24 => [(true, true), (true, true), (false, true), (false, true), (false, true)]
  | 25 => [(false, true), (false, true), (true, true), (false, true), (false, true)]
  | 26 => [(true, true), (false, true), (true, true), (false, true), (false, true)]
  | 27 => [(false, true), (true, true), (true, true), (false, true), (false, true)]
  | 28 => [(true, true), (false, true), (false, true), (true, true), (false, true)]
  | 29 => [(false, true), (true, true), (false, true), (true, true), (false, true)]
  | 30 => [(false, true), (true, true), (true, true), (false, true), (true, true)]
  | 31 => [(true, true), (true, true), (false, true), (true, true), (true, true)]
  | 32 => [(true, true), (true, true), (false, true), (false, true), (false, true), (false, true)]
  | 33 => [(false, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | 34 => [(true, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | _ => [(false, true), (false, true), (true, true), (true, true), (false, true), (false, true)]

private def baseImage : Fin 36 → Fin 6156
  | 0 => 0
  | 1 => 4909
  | 2 => 5545
  | 3 => 2075
  | 4 => 1413
  | 5 => 3647
  | 6 => 509
  | 7 => 2399
  | 8 => 398
  | 9 => 2344
  | 10 => 6075
  | 11 => 4302
  | 12 => 4042
  | 13 => 5774
  | 14 => 4143
  | 15 => 3343
  | 16 => 3791
  | 17 => 1542
  | 18 => 1249
  | 19 => 1342
  | 20 => 5782
  | 21 => 3193
  | 22 => 1480
  | 23 => 4317
  | 24 => 2313
  | 25 => 23
  | 26 => 4134
  | 27 => 1782
  | 28 => 5486
  | 29 => 4258
  | 30 => 5963
  | 31 => 1347
  | 32 => 1791
  | 33 => 4977
  | 34 => 5255
  | _ => 1633

private theorem baseImage_injective : Function.Injective baseImage := by
  change ∀ i j, baseImage i = baseImage j → i = j
  decide +kernel

private theorem base_cert : ∀ i : Fin 36,
    eval pairPermutation (baseWord i) 0 = baseImage i := by
  apply allFin
  decide +kernel

private def stabilizerWord : Fin 60 → Word Bool
  | 0 => []
  | 1 => [(false, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | 2 => [(true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true)]
  | 3 => [(true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true)]
  | 4 => [(true, true), (true, true), (false, true), (false, true), (true, true), (true, true), (false, true)]
  | 5 => [(true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true)]
  | 6 => [(false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | 7 => [(false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true)]
  | 8 => [(false, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 9 => [(false, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true)]
  | 10 => [(false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true)]
  | 11 => [(true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true)]
  | 12 => [(false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true)]
  | 13 => [(false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true)]
  | 14 => [(false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true)]
  | 15 => [(true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true)]
  | 16 => [(true, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (true, true)]
  | 17 => [(true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true)]
  | 18 => [(true, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (true, true), (false, true)]
  | 19 => [(false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | 20 => [(true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true)]
  | 21 => [(true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true)]
  | 22 => [(true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true), (true, true), (true, true)]
  | 23 => [(false, true), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true)]
  | 24 => [(false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 25 => [(true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (false, true)]
  | 26 => [(false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true)]
  | 27 => [(true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | 28 => [(false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true)]
  | 29 => [(false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true)]
  | 30 => [(false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true)]
  | 31 => [(false, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true)]
  | 32 => [(false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true)]
  | 33 => [(false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true)]
  | 34 => [(false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 35 => [(true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | 36 => [(true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | 37 => [(true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true)]
  | 38 => [(false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true)]
  | 39 => [(false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | 40 => [(true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true)]
  | 41 => [(false, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true)]
  | 42 => [(true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | 43 => [(true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | 44 => [(true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true)]
  | 45 => [(false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (true, true)]
  | 46 => [(true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true)]
  | 47 => [(true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 48 => [(false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (false, true)]
  | 49 => [(false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true)]
  | 50 => [(false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true)]
  | 51 => [(true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true)]
  | 52 => [(false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true)]
  | 53 => [(true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | 54 => [(true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true)]
  | 55 => [(true, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | 56 => [(false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true)]
  | 57 => [(true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 58 => [(true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | _ => [(false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true)]

private def stabilizerImage : Fin 60 → Fin 6156
  | 0 => 2
  | 1 => 5321
  | 2 => 946
  | 3 => 5178
  | 4 => 3800
  | 5 => 394
  | 6 => 4354
  | 7 => 6106
  | 8 => 1513
  | 9 => 4806
  | 10 => 4149
  | 11 => 308
  | 12 => 154
  | 13 => 3702
  | 14 => 5202
  | 15 => 4650
  | 16 => 4866
  | 17 => 625
  | 18 => 4039
  | 19 => 1799
  | 20 => 5969
  | 21 => 4743
  | 22 => 2431
  | 23 => 5018
  | 24 => 2149
  | 25 => 3813
  | 26 => 5612
  | 27 => 6024
  | 28 => 27
  | 29 => 218
  | 30 => 3569
  | 31 => 5146
  | 32 => 5641
  | 33 => 3285
  | 34 => 95
  | 35 => 2094
  | 36 => 3457
  | 37 => 622
  | 38 => 3771
  | 39 => 2023
  | 40 => 3711
  | 41 => 5405
  | 42 => 4271
  | 43 => 669
  | 44 => 3429
  | 45 => 2120
  | 46 => 499
  | 47 => 413
  | 48 => 2234
  | 49 => 2330
  | 50 => 734
  | 51 => 4767
  | 52 => 1170
  | 53 => 175
  | 54 => 4748
  | 55 => 1320
  | 56 => 3121
  | 57 => 4763
  | 58 => 924
  | _ => 790

private theorem stabilizerImage_injective : Function.Injective stabilizerImage := by
  change ∀ i j, stabilizerImage i = stabilizerImage j → i = j
  decide +kernel

private theorem stabilizer_cert : ∀ i : Fin 60,
    eval pairPermutation (stabilizerWord i) 2 = stabilizerImage i := by
  apply allFin
  decide +kernel

private theorem stabilizer_fixes : ∀ i : Fin 60,
    eval pairPermutation (stabilizerWord i) 0 = 0 := by
  apply allFin
  decide +kernel

private theorem word_mem (w : Word Bool) : eval pairGenerator w ∈ thirdLocalModel := by
  have hg (b : Bool) : pairGenerator b ∈ thirdLocalModel := by
    cases b <;> apply subset_closure <;> simp [pairGenerator]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply thirdLocalModel.mul_mem _ ih
    split
    · exact hg a.1
    · exact thirdLocalModel.inv_mem (hg a.1)

private def witness (i : Fin 36 × Fin 60) : thirdLocalModel :=
  ⟨eval pairGenerator (baseWord i.1) * eval pairGenerator (stabilizerWord i.2),
    thirdLocalModel.mul_mem (word_mem _) (word_mem _)⟩

private theorem witness_injective : Function.Injective witness := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hv := congrArg (fun x : thirdLocalModel => (x : Model)) he
  change eval pairGenerator (baseWord i) * eval pairGenerator (stabilizerWord j) =
    eval pairGenerator (baseWord k) * eval pairGenerator (stabilizerWord l) at hv
  have hzero := congrArg (fun x : Model => embedding x 0) hv
  simp only [map_mul,Equiv.Perm.mul_apply,embedding_eval,stabilizer_fixes,base_cert] at hzero
  have hik : i = k := baseImage_injective hzero
  subst k
  have hjl := mul_left_cancel hv
  have htwo := congrArg (fun x : Model => embedding x 2) hjl
  simp only [embedding_eval,stabilizer_cert] at htwo
  exact Prod.ext rfl (stabilizerImage_injective htwo)

/-- This lower bound is proved inside the actual model by distinct words. -/
theorem thirdLocalModel_card_lower : 2160 ≤ Nat.card thirdLocalModel := by
  have hc := Nat.card_le_card_of_injective witness witness_injective
  simpa only [Nat.card_prod,Nat.card_fin] using hc

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
