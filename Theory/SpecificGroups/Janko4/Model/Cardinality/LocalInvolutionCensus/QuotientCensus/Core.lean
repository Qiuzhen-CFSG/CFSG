module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Counting
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Theory.GroupTheory.SylowElementConjugacy
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Arithmetic and finite-table principles for the max2 quotient census

A 144-bit word encodes the actual twelve-dimensional binary matrix, with
row i in bits 12i through 12i+11. Decoding is injective, and the existing
packed-row theorem certifies matrix products. Multiplication programs give
actual elements of Q; subgroup trees, sorted codes, and closed tables then
certify membership, lower bounds, and exhaustive coverage respectively.

The marked elements are proved equal to the four published quotient lifts.
These finite certificates support the local counts motivated by
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
The underlying ATLAS provenance is in `TwoCoreCentralizer/source/`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound QuotientOrderCertificate

def decode (v : BitVec 144) : QuotientMatrix :=
  fun i j => if v.getLsbD (12 * i.val + j.val) then 1 else 0

def rows (v : BitVec 144) : Vector ℕ 12 :=
  #v[(v.toNat >>> 0) % 4096, (v.toNat >>> 12) % 4096, (v.toNat >>> 24) % 4096, (v.toNat >>> 36) % 4096, (v.toNat >>> 48) % 4096, (v.toNat >>> 60) % 4096, (v.toNat >>> 72) % 4096, (v.toNat >>> 84) % 4096, (v.toNat >>> 96) % 4096, (v.toNat >>> 108) % 4096, (v.toNat >>> 120) % 4096, (v.toNat >>> 132) % 4096]

theorem rows_get (v : BitVec 144) (i : Fin 12) :
    (rows v).get i = (v.toNat >>> (12 * i.val)) % 4096 := by
  fin_cases i <;> rfl

theorem decode_eq (v : BitVec 144) : decode v = quotientDecode (rows v) := by
  funext i j
  change (if v.getLsbD (12 * i.val + j.val) then (1 : ZMod 2) else 0) =
    (if ((rows v).get i).testBit j.val then 1 else 0)
  rw [rows_get]
  change (if v.toNat.testBit (12 * i.val + j.val) then (1 : ZMod 2) else 0) =
    (if ((v.toNat >>> (12 * i.val)) % 2^12).testBit j.val then 1 else 0)
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

theorem decode_injective : Function.Injective decode := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 12 := ⟨k / 12, by omega⟩
  let j : Fin 12 := ⟨k % 12, Nat.mod_lt _ (by decide)⟩
  have he := congrFun (congrFun h i) j
  have hidx : 12 * i.val + j.val = k := by dsimp [i, j]; omega
  change (if a.getLsbD (12 * i.val + j.val) then (1 : ZMod 2) else 0) =
    (if b.getLsbD (12 * i.val + j.val) then 1 else 0) at he
  rw [hidx] at he
  cases ha : a.getLsbD k <;> cases hb : b.getLsbD k <;> simp_all

abbrev mulCheck (a b c : BitVec 144) : Prop :=
  ∀ i : Fin 12, packedRow ((rows a).get i) (rows b) = (rows c).get i

theorem mulCheck_sound {a b c : BitVec 144} (h : mulCheck a b c) :
    decode a * decode b = decode c := by
  rw [decode_eq, decode_eq, decode_eq]
  exact mul_eq_of_packed _ _ _ h

def basic : Fin 4 → Q :=
  ![1, ⟨quotientX, quotientX_mem⟩, ⟨quotientY, quotientY_mem⟩,
    ⟨quotientY⁻¹, quotientSubgroup.inv_mem quotientY_mem⟩]

theorem forall_fin_of_range {n : ℕ} [NeZero n]
    (P : Fin n → Prop) [DecidablePred P]
    (h : (List.range n).all (fun i => decide (P (Fin.ofNat n i))) = true) : ∀ i, P i := by
  intro i
  have hi := of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simpa only [Fin.ofNat_val_eq_self] using hi

/-- A multiplication program beginning with the identity and the actual quotient generators. -/
theorem program_membership {n : ℕ} (code : Fin n → BitVec 144)
    (left right : Fin n → Fin n)
    (hbase : ∀ i, i.val < 4 → ((basic (Fin.ofNat 4 i.val)).val : QuotientMatrix) = decode (code i))
    (hlt : ∀ i, 4 ≤ i.val → left i < i ∧ right i < i)
    (hmul : ∀ i, 4 ≤ i.val → mulCheck (code (left i)) (code (right i)) (code i)) :
    ∀ i, ∃ g : Q, (g.val : QuotientMatrix) = decode (code i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i.val < 4
    · exact ⟨basic (Fin.ofNat 4 i.val), hbase i hi⟩
    · have hi' : 4 ≤ i.val := by omega
      obtain ⟨a, ha⟩ := ih (left i) (hlt i hi').1
      obtain ⟨b, hb⟩ := ih (right i) (hlt i hi').2
      refine ⟨a * b, ?_⟩
      change (a.val : QuotientMatrix) * (b.val : QuotientMatrix) = _
      rw [ha, hb]
      exact mulCheck_sound (hmul i hi')

/-- The actual four images expressed entirely in the small matrix subgroup. -/
def marked : Fin 4 → Q :=
  ![1, basic 1, (basic 1 * basic 2)^7, ((basic 1 * basic 2)^5 * basic 2)^4]

theorem marked_eq (j : Fin 4) : marked j = q (lift j) := by
  apply Subtype.ext
  change (marked j).val = Coordinates.localQuotientMap (sourceSubgroupEquivLocal (sourceLift j))
  rw [Coordinates.localQuotientMap_sourceEquiv]
  fin_cases j <;>
    simp [marked, basic, sourceLift, map_pow, map_mul, quotientMap_sourceX, quotientMap_sourceY]

/-- A finite multiplication tree remains in every subgroup containing its generators. -/
theorem tree_mem {n k : ℕ} [NeZero n] (K : Subgroup Q)
    (gen : Fin k → Q) (table : Fin n → Q)
    (parent : Fin n → Fin n) (letter : Fin n → Fin k)
    (hgen : ∀ a, gen a ∈ K) (hroot : table 0 = 1)
    (hlt : ∀ i, i ≠ 0 → parent i < i)
    (hedge : ∀ i, i ≠ 0 → table (parent i) * gen (letter i) = table i) :
    ∀ i, table i ∈ K := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · simpa only [hi, hroot] using K.one_mem
    · rw [← hedge i hi]
      exact K.mul_mem (ih (parent i) (hlt i hi)) (hgen _)

/-- Sorting codes provides a linear-size certificate of distinctness. -/
theorem table_injective {n : ℕ} (table : Fin (n+1) → Q)
    (code : Fin (n+1) → BitVec 144)
    (hval : ∀ i, (table i).val.val = decode (code i))
    (hsorted : ∀ i : Fin n, (code i.castSucc).toNat < (code i.succ).toNat) :
    Function.Injective table := by
  have hinj := (Fin.strictMono_iff_lt_succ (f := fun i => (code i).toNat) |>.mpr hsorted).injective
  intro i j hij
  apply hinj
  have he := congrArg (fun g : Q => g.val.val) hij
  rw [hval, hval] at he
  exact congrArg BitVec.toNat (decode_injective he)

/-- A table stable under generators and their inverses covers the generated subgroup. -/
theorem table_covers {n k : ℕ} [NeZero n] (gen : Fin k → Q) (table : Fin n → Q)
    (step stepInv : Fin k → Fin n → Fin n)
    (hroot : table 0 = 1)
    (hstep : ∀ a i, table i * gen a = table (step a i))
    (hstepInv : ∀ a i, table i * (gen a)⁻¹ = table (stepInv a i)) :
    ∀ g ∈ Subgroup.closure (Set.range gen), ∃ i, g = table i := by
  intro g hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, hroot.symm⟩
  | mul_right x hx y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨step a i, hstep a i⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨stepInv a i, hstepInv a i⟩

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
