module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.MathieuAbsorption.Quotient
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.SubgroupEnumeration
import Mathlib.Tactic.FinCases

/-!
# Two permuting Mathieu pairs whose products generate the local quotient

The two elementary-nine subgroups below permute with the specified Sylow
subgroup. Their products together generate M₂₄. The finite certificates use
four lifted Sylow generators and nine coset representatives for each pair.
All permutation identities are checked by the kernel. GAP discovered the
words but supplies no mathematical premise.

Consequently the two full inverse images together generate the literal J₄
max1 subgroup. This is relevant to the proposed universal max4 absorption:
one must not put both products into one proper local overlap.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), where the final irreducibility sieve is
retained. This module does not assert a max4 containment or its negation.
-/

public section

set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true

open Subgroup
open scoped Pointwise
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption.FixedSylowObstruction

attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup

private def uPerm00 : Equiv.Perm (Fin 24) where
  toFun := ![22, 1, 2, 5, 14, 9, 16, 7, 8, 3, 10, 11, 23, 4, 13, 18, 17, 6, 20, 12, 15, 0, 21, 19]
  invFun := ![21, 1, 2, 9, 13, 3, 17, 7, 8, 5, 10, 11, 19, 14, 4, 20, 6, 16, 15, 23, 18, 22, 0, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def uPerm01 : Equiv.Perm (Fin 24) where
  toFun := ![15, 1, 2, 22, 4, 21, 17, 10, 7, 0, 8, 11, 23, 13, 14, 9, 6, 16, 3, 12, 5, 20, 18, 19]
  invFun := ![9, 1, 2, 18, 4, 20, 16, 8, 10, 15, 7, 11, 19, 13, 14, 0, 17, 6, 22, 23, 21, 5, 3, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def uPerm10 : Equiv.Perm (Fin 24) where
  toFun := ![5, 21, 11, 16, 20, 17, 10, 1, 12, 6, 9, 18, 14, 15, 8, 23, 22, 0, 2, 4, 19, 7, 3, 13]
  invFun := ![17, 7, 18, 22, 19, 0, 9, 21, 14, 10, 6, 2, 8, 23, 12, 13, 3, 5, 11, 20, 4, 1, 16, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def uPerm11 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 9, 23, 16, 5, 14, 7, 18, 12, 8, 6, 2, 4, 11, 20, 13, 17, 10, 3, 22, 21, 15, 19]
  invFun := ![0, 1, 12, 19, 13, 5, 11, 7, 10, 2, 18, 14, 9, 16, 6, 22, 4, 17, 8, 23, 15, 21, 20, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def uPerm (k j : Fin 2) : Equiv.Perm (Fin 24) :=
  ![![uPerm00, uPerm01], ![uPerm10, uPerm11]] k j

private def uWord : Fin 2 → Fin 2 → List (Fin 4) :=
  ![![[2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 2, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1], [1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1]], ![[2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1], [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3]]]

private theorem uPerm_word (k j : Fin 2) :
    uPerm k j = evalWord starAlphabet (uWord k j) := by
  fin_cases k <;> fin_cases j <;> decide +kernel

private def u (k j : Fin 2) : StarGroup :=
  ⟨uPerm k j, by
    rw [uPerm_word]
    exact StarOrderCertificate.word_mem _ _ starAlphabet_mem _⟩

private def elementary (k : Fin 2) : Subgroup StarGroup :=
  zpowers (u k 0) ⊔ zpowers (u k 1)

private theorem u_order (k j : Fin 2) : orderOf (u k j) = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    fin_cases k <;> fin_cases j <;> decide +kernel
  · intro h
    have hn : (u k j : Equiv.Perm (Fin 24)) ≠ 1 := by
      fin_cases k <;> fin_cases j <;> decide +kernel
    exact hn (congrArg Subtype.val h)

private theorem u_commute (k : Fin 2) : Commute (u k 0) (u k 1) := by
  apply Subtype.ext
  fin_cases k <;> decide +kernel

private theorem u_not_mem (k : Fin 2) : u k 1 ∉ zpowers (u k 0) := by
  rw [mem_zpowers_iff_mem_range_orderOf, u_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 3,
      (u k 1 : Equiv.Perm (Fin 24)) ≠ (u k 0 : Equiv.Perm (Fin 24)) ^ i.val := by
    fin_cases k <;> decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ (congrArg Subtype.val he).symm

private theorem elementary_properties (k : Fin 2) :
    IsElementaryAbelian 3 (elementary k) ∧ Nat.card (elementary k) = 9 := by
  let : IsElementaryAbelian 3 (zpowers (u k 0)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (u_order k 0 ▸ pow_orderOf_eq_one (u k 0))
  have hc : Nat.card (zpowers (u k 0)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, u_order]; norm_num
  have hfix : zpowers (u k 0) ≤ centralizer ({u k 1} : Set StarGroup) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr (u_commute k).eq
  exact IsElementaryAbelian.fixed_join_card (zpowers (u k 0)) (u k 1) (u_order k 1)
    ((zpowers (u k 0)).disjoint_zpowers_of_prime_order_not_mem _ (u_order k 1) (u_not_mem k))
    hfix hc

private def representative (k : Fin 2) (i : Fin 9) : StarGroup :=
  u k 0 ^ (i.val % 3) * u k 1 ^ (i.val / 3)

private theorem representative_mem (k : Fin 2) (i : Fin 9) :
    representative k i ∈ elementary k :=
  (elementary k).mul_mem
    ((elementary k).pow_mem (mem_sup_left (mem_zpowers (u k 0))) _)
    ((elementary k).pow_mem (mem_sup_right (mem_zpowers (u k 1))) _)

private theorem representative_surjective (k : Fin 2) (x : StarGroup)
    (hx : x ∈ elementary k) : ∃ i, representative k i = x := by
  let f : Fin 9 → elementary k := fun i => ⟨representative k i, representative_mem k i⟩
  have hi : Function.Injective f := by
    intro i j he
    have hh : Function.Injective (fun i : Fin 9 => (representative k i : Equiv.Perm (Fin 24))) := by
      fin_cases k <;> decide +kernel
    exact hh (congrArg (fun v : elementary k => (v.val : Equiv.Perm (Fin 24))) he)
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, by rw [Nat.card_fin, (elementary_properties k).2]⟩).2
  obtain ⟨i, he⟩ := hs ⟨x, hx⟩
  exact ⟨i, congrArg Subtype.val he⟩

private def nextRepresentative : Fin 2 → Fin 9 → Fin 4 → Fin 9 :=
  ![![![0, 0, 0, 0], ![2, 2, 1, 2], ![1, 1, 2, 1], ![4, 4, 3, 6], ![3, 3, 4, 8], ![5, 5, 5, 7], ![8, 8, 6, 3], ![7, 7, 7, 5], ![6, 6, 8, 4]], ![![0, 0, 0, 0], ![1, 2, 1, 1], ![2, 1, 2, 2], ![3, 3, 6, 3], ![4, 5, 7, 4], ![5, 4, 8, 5], ![6, 6, 3, 6], ![7, 8, 4, 7], ![8, 7, 5, 8]]]

private def residualWord : Fin 2 → Fin 9 → Fin 4 → List (Fin 4) :=
  ![![![[0], [1], [2], [3]], ![[1, 3, 2, 3, 1, 0], [0, 3, 2, 3, 0, 1, 3, 2, 3], [2, 0, 2, 0], [1, 3, 2, 3, 1, 3, 0, 2, 0]], ![[0, 1, 3, 2, 3, 1], [3, 2, 3, 1, 0, 3, 2, 3, 0], [0, 2, 0], [1, 3, 0, 2, 3, 1, 3, 0, 2]], ![[1, 3, 2, 3, 1, 0, 2], [2, 3, 1, 3, 0, 2, 0], [1, 0, 1, 3, 0, 3, 2, 0, 2, 0], [2, 3, 1, 3, 2, 3, 0]], ![[2, 0, 1, 3, 2, 3, 1], [0, 2, 3, 1, 3, 0, 2], [1, 3, 0, 2, 3, 1, 3, 0, 3], [2, 0, 3, 0, 1, 3, 2, 0, 3]], ![[2, 0, 2], [3, 1, 3], [1, 3, 2, 3, 1], [0, 2, 0, 2, 3, 0, 1]], ![[1, 0, 1, 3, 0, 3, 0, 2], [2, 3, 0, 1, 3, 1, 2], [1, 3, 0, 2, 3, 1, 3, 0, 3, 0, 2, 0], [0, 3, 2, 3, 1, 3, 2]], ![[1, 0, 1, 3, 0, 3, 0], [1, 3, 1, 0, 3, 2, 0, 2, 0], [1, 3, 2, 3, 1, 2], [1, 0, 3, 2, 0, 2, 0]], ![[1, 0, 1, 3, 0, 3, 2, 0], [2, 1, 3, 1, 0, 3, 2], [1, 0, 1, 3, 0, 3], [3, 0, 2, 3, 1, 0, 3, 0, 2]]], ![![[0], [1], [2], [3]], ![[1, 2, 3, 1, 0, 2, 0], [0, 1, 3, 2, 3, 0, 2], [1, 0, 1, 0, 3, 2, 3, 2, 0, 2, 0], [2, 0, 2]], ![[1, 0, 1, 2, 3, 2, 0], [2, 0, 3, 2, 3, 1, 0], [1, 3, 2, 3, 1, 3, 2, 3, 0, 2, 0], [0, 1, 3, 1, 3, 0, 3]], ![[3, 0, 3, 2, 0, 2, 0], [3, 2, 3, 1, 3, 2, 3, 2, 0, 2], [3, 2], [3, 2, 3, 2]], ![[1, 3, 1, 3, 0, 3, 0], [0, 2, 3, 2, 3, 0, 1, 3], [1, 0, 1, 3, 2, 3], [3, 0, 3, 2, 0, 2]], ![[1, 0, 1, 0, 3], [3, 1, 0, 3, 2, 3, 2, 0], [3, 2, 3, 0, 1, 3, 1, 0], [1, 3, 2, 3, 1, 3, 0, 3, 2, 0]], ![[2, 0, 2, 0], [3, 1, 0, 3, 2, 0, 2], [2, 3], [2, 3, 2]], ![[1, 3, 0, 2, 3, 1, 0, 2], [3, 0, 1], [3, 2, 3, 1, 0, 1], [3, 0, 3]], ![[1, 0, 1, 0, 3, 2, 3, 2], [1, 0, 3], [0, 1, 3, 1, 0, 3, 2, 3], [2, 1, 3, 1, 2]]]]

private theorem representative_step (k : Fin 2) (i : Fin 9) (j : Fin 4) :
    representative k i * sylowGenerator j =
      evalWord sylowGenerator (residualWord k i j) *
        representative k (nextRepresentative k i j) := by
  apply Subtype.ext
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide +kernel

private theorem sylowGenerator_inv (j : Fin 4) : (sylowGenerator j)⁻¹ = sylowGenerator j := by
  apply Subtype.ext
  fin_cases j <;> decide +kernel

private theorem representative_sylow (k : Fin 2) (x : StarGroup)
    (hx : x ∈ elementary k) (j : Fin 4) :
    x * sylowGenerator j ∈ (sylowCandidate : Set StarGroup) * (elementary k : Set StarGroup) := by
  obtain ⟨i, rfl⟩ := representative_surjective k x hx
  rw [representative_step]
  exact Set.mul_mem_mul
    (SubgroupEnumeration.evalWord_mem sylowGenerator sylowCandidate
      (fun j => Subgroup.subset_closure ⟨j, rfl⟩) _)
    (representative_mem _ _)

private theorem elementary_permutes (k : Fin 2) :
    (elementary k : Set StarGroup) * (sylowCandidate : Set StarGroup) =
      (sylowCandidate : Set StarGroup) * (elementary k : Set StarGroup) := by
  have hmain (s : StarGroup) (hs : s ∈ sylowCandidate) :
      ∀ x ∈ elementary k,
        x * s ∈ (sylowCandidate : Set StarGroup) * (elementary k : Set StarGroup) := by
    induction hs using Subgroup.closure_induction_left with
    | one =>
      intro x hx
      exact ⟨1, sylowCandidate.one_mem, x, hx, by simp⟩
    | mul_left y hy s hs ih =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      obtain ⟨t, ht, v, hv, he⟩ := representative_sylow k x hx j
      obtain ⟨t', ht', v', hv', he'⟩ := ih v hv
      change t * v = x * sylowGenerator j at he
      change t' * v' = v * s at he'
      refine ⟨t * t', sylowCandidate.mul_mem ht ht', v', hv', ?_⟩
      calc
        t * t' * v' = t * (t' * v') := mul_assoc _ _ _
        _ = t * (v * s) := by rw [he']
        _ = x * (sylowGenerator j * s) := by rw [← mul_assoc, he, mul_assoc]
    | inv_mul_cancel y hy s hs ih =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      rw [sylowGenerator_inv]
      obtain ⟨t, ht, v, hv, he⟩ := representative_sylow k x hx j
      obtain ⟨t', ht', v', hv', he'⟩ := ih v hv
      change t * v = x * sylowGenerator j at he
      change t' * v' = v * s at he'
      refine ⟨t * t', sylowCandidate.mul_mem ht ht', v', hv', ?_⟩
      calc
        t * t' * v' = t * (t' * v') := mul_assoc _ _ _
        _ = t * (v * s) := by rw [he']
        _ = x * (sylowGenerator j * s) := by rw [← mul_assoc, he, mul_assoc]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, s, hs, rfl⟩
    exact hmain s hs x hx
  · rintro _ ⟨s, hs, x, hx, rfl⟩
    obtain ⟨t, ht, v, hv, he⟩ := hmain s⁻¹ (sylowCandidate.inv_mem hs) x⁻¹
      ((elementary k).inv_mem hx)
    refine ⟨v⁻¹, (elementary k).inv_mem hv, t⁻¹, sylowCandidate.inv_mem ht, ?_⟩
    simpa using congrArg Inv.inv he

private def jointGenerator : Fin 8 → StarGroup :=
  ![sylowGenerator 0, sylowGenerator 1, sylowGenerator 2, sylowGenerator 3,
    u 0 0, u 0 1, u 1 0, u 1 1]

private def jointAlphabet (i : Fin 16) : StarGroup :=
  if h : i.val < 8 then jointGenerator ⟨i.val, h⟩
    else (jointGenerator ⟨i.val - 8, by omega⟩)⁻¹

private def generationWord0 : List (Fin 16) :=
  [10, 14, 7, 12, 8, 6, 13, 14, 4, 0, 7, 11, 13, 6, 13, 15, 6, 0, 12, 13, 7, 1, 13, 2, 0, 11, 14, 11, 6]

private def generationWord1 : List (Fin 16) :=
  [14, 15, 14, 5, 14, 12, 15, 12, 5, 8, 14, 13, 14, 15, 12, 6, 5, 15, 6, 1, 12, 13, 7, 12, 6, 11, 13, 14, 0, 9, 4, 9, 4]

private theorem generation_first : starFirst = evalWord jointAlphabet generationWord0 := by
  apply Subtype.ext
  decide +kernel

private theorem generation_second : starSecond = evalWord jointAlphabet generationWord1 := by
  apply Subtype.ext
  decide +kernel

private theorem joint_generation :
    (elementary 0 ⊔ sylowCandidate) ⊔ (elementary 1 ⊔ sylowCandidate) = ⊤ := by
  let K := (elementary 0 ⊔ sylowCandidate) ⊔ (elementary 1 ⊔ sylowCandidate)
  have hS : sylowCandidate ≤ K := le_sup_right.trans le_sup_left
  have hE0 : elementary 0 ≤ K := le_sup_left.trans le_sup_left
  have hE1 : elementary 1 ≤ K := le_sup_left.trans le_sup_right
  have hj (i : Fin 8) : jointGenerator i ∈ K := by
    fin_cases i
    · exact hS (show _ ∈ Subgroup.closure (Set.range sylowGenerator) from
        Subgroup.subset_closure ⟨0, rfl⟩)
    · exact hS (show _ ∈ Subgroup.closure (Set.range sylowGenerator) from
        Subgroup.subset_closure ⟨1, rfl⟩)
    · exact hS (show _ ∈ Subgroup.closure (Set.range sylowGenerator) from
        Subgroup.subset_closure ⟨2, rfl⟩)
    · exact hS (show _ ∈ Subgroup.closure (Set.range sylowGenerator) from
        Subgroup.subset_closure ⟨3, rfl⟩)
    · exact hE0 (mem_sup_left (mem_zpowers (u 0 0)))
    · exact hE0 (mem_sup_right (mem_zpowers (u 0 1)))
    · exact hE1 (mem_sup_left (mem_zpowers (u 1 0)))
    · exact hE1 (mem_sup_right (mem_zpowers (u 1 1)))
  have ha (i : Fin 16) : jointAlphabet i ∈ K := by
    unfold jointAlphabet
    split
    · exact hj _
    · exact K.inv_mem (hj _)
  have hx : starFirst ∈ K := by
    rw [generation_first]
    exact SubgroupEnumeration.evalWord_mem jointAlphabet K ha _
  have hy : starSecond ∈ K := by
    rw [generation_second]
    exact SubgroupEnumeration.evalWord_mem jointAlphabet K ha _
  have hh : StarGroup ≤ K.map StarGroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases (show g = starX ∨ g = starY from by simpa using hg) with rfl | rfl
    · exact ⟨starFirst, hx, rfl⟩
    · exact ⟨starSecond, hy, rfl⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, hy, he⟩ := hh x.property
  exact (Subtype.ext he : y = x) ▸ hy

/-- The exact image of each certified star elementary-nine subgroup. -/
noncomputable def quotientNine (k : Fin 2) : Subgroup Sporadic.Mathieu.M24 :=
  (elementary k).map starGroupEquivM24.toMonoidHom

/-- Both groups are elementary abelian of order nine in the native carrier. -/
theorem quotientNine_properties (k : Fin 2) :
    IsElementaryAbelian 3 (quotientNine k) ∧ Nat.card (quotientNine k) = 3 ^ 2 := by
  let _ := (elementary_properties k).1
  constructor
  · exact IsElementaryAbelian.map starGroupEquivM24.toMonoidHom
  · rw [quotientNine, card_map_of_injective starGroupEquivM24.injective,
      (elementary_properties k).2]
    norm_num

private theorem standardSylow_eq_map :
    standardSylow.toSubgroup = sylowCandidate.map starGroupEquivM24.toMonoidHom := by
  change (Janko4.OuterReduction.OddIndex.localTwoSubgroup.map projection) = _
  have he : projection = starGroupEquivM24.toMonoidHom.comp
      Janko4.OuterReduction.OddIndex.localProjection := by
    apply MonoidHom.eq_of_eqOn_dense
      (Janko4.Cardinality.localXY_generate Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    intro l hl
    rcases (show l = Janko4.Cardinality.localX _ _ ∨
        l = Janko4.Cardinality.localY _ _ from by simpa using hl) with rfl | rfl
    · change Janko4.LocalStructure.localQuotientEquivM24 _ _
        (QuotientGroup.mk' _ (Janko4.Cardinality.localX _ _)) =
        starGroupEquivM24 (Janko4.OuterReduction.OddIndex.localProjection _)
      rw [Janko4.LocalStructure.localQuotientEquivM24_apply,
        Janko4.OuterReduction.OddIndex.localProjection_x]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_x _ _
    · change Janko4.LocalStructure.localQuotientEquivM24 _ _
        (QuotientGroup.mk' _ (Janko4.Cardinality.localY _ _)) =
        starGroupEquivM24 (Janko4.OuterReduction.OddIndex.localProjection _)
      rw [Janko4.LocalStructure.localQuotientEquivM24_apply,
        Janko4.OuterReduction.OddIndex.localProjection_y]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_y _ _
  rw [he, ← Subgroup.map_map]
  congr 1
  exact Subgroup.map_comap_eq_self_of_surjective
    Janko4.OuterReduction.OddIndex.localProjection_surjective _

/-- The exact setwise product commutes with the published standard Sylow.
Neither factor is asserted to normalize the other. -/
theorem quotientNine_permutes (k : Fin 2) :
    (quotientNine k : Set Sporadic.Mathieu.M24) * (standardSylow : Set Sporadic.Mathieu.M24) =
      (standardSylow : Set Sporadic.Mathieu.M24) * (quotientNine k : Set Sporadic.Mathieu.M24) := by
  have he := congrArg (Set.image starGroupEquivM24.toMonoidHom) (elementary_permutes k)
  change (quotientNine k : Set Sporadic.Mathieu.M24) *
    (standardSylow.toSubgroup : Set Sporadic.Mathieu.M24) =
      (standardSylow.toSubgroup : Set Sporadic.Mathieu.M24) * (quotientNine k : Set Sporadic.Mathieu.M24)
  rw [standardSylow_eq_map]
  simpa only [quotientNine, coe_map, Set.image_mul] using he

/-- The two admissible quotient products together generate all of M₂₄. -/
theorem quotient_products_generate :
    (quotientNine 0 ⊔ standardSylow.toSubgroup) ⊔
      (quotientNine 1 ⊔ standardSylow.toSubgroup) = ⊤ := by
  rw [standardSylow_eq_map, quotientNine, quotientNine,
    ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup, joint_generation,
    map_top_of_surjective _ starGroupEquivM24.surjective]

/-- Their full inverse images generate the literal max1 subgroup, including
its binary kernel. -/
theorem preimage_products_generate :
    preimage (quotientNine 0 ⊔ standardSylow.toSubgroup) ⊔
      preimage (quotientNine 1 ⊔ standardSylow.toSubgroup) = Local := by
  unfold preimage
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq _ _ _ projection_surjective,
    quotient_products_generate, comap_top, ← MonoidHom.range_eq_map, range_subtype]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption.FixedSylowObstruction
