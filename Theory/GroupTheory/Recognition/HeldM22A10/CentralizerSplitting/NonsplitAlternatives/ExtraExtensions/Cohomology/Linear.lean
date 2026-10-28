module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.FactorSets
/-!
# Binary linear certificates and elementary factor-set operations

A natural-number mask denotes a linear form over F₂. XOR is addition of
forms. A row certificate records a cocycle equation plus previously proved
rows; a triangular pivot certificate then proves that vanishing on the free
coordinates forces a cocycle to vanish. All certificate checks are ordinary
kernel reductions. Products and coboundaries supply the change of section.

This supports the finite cohomology calculation for the auxiliary actions in
Huppert--Blackburn III, XII.1.18(b), p.314.
-/

@[expose] public section
open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology

def ev {n : ℕ} (x : Fin n → ZMod 2) (r : ℕ) : ZMod 2 :=
  ∑ i, if r.testBit i.val then x i else 0

lemma ev_zero {n : ℕ} (x : Fin n → ZMod 2) : ev x 0 = 0 := by simp [ev]
lemma ev_xor {n : ℕ} (x : Fin n → ZMod 2) (r s : ℕ) :
    ev x (r ^^^ s) = ev x r + ev x s := by
  simp only [ev, ← Finset.sum_add_distrib, Nat.testBit_xor]
  apply Finset.sum_congr rfl
  intro i _
  cases r.testBit i.val <;> cases s.testBit i.val <;> simp [CharTwo.add_self_eq_zero]
lemma ev_unit {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) : ev x (2 ^ i.val) = x i := by
  simp [ev, Nat.testBit_two_pow, Fin.val_inj]
lemma ev_top {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) (r : ℕ)
    (hr : r < 2 ^ (i.val + 1)) (hi : r.testBit i.val = true)
    (hx : ∀ j : Fin n, j < i → x j = 0) : ev x r = x i := by
  rw [ev, Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    by_cases hlt : j < i
    · simp [hx j hlt]
    · have hpow : 2 ^ (i.val + 1) ≤ 2 ^ j.val := Nat.pow_le_pow_right (by decide) (by omega)
      simp [Nat.testBit_lt_two_pow (hr.trans_le hpow)]
  · simp

open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
variable {α : SymmetricFour →* MulAut BinaryFour}

def times (c d : FactorSet α) : FactorSet α where
 value s t := c.value s t * d.value s t
 one_left s := by simp [c.one_left, d.one_left]
 one_right s := by simp [c.one_right, d.one_right]
 cocycle s t r := by
  rw [mul_mul_mul_comm, c.cocycle, d.cocycle, map_mul]
  ac_rfl

def cob (b : SymmetricFour → BinaryFour) (hb : b 1 = 1) : FactorSet α where
 value s t := b s * α s (b t) * (b (s*t))⁻¹
 one_left s := by simp [hb]
 one_right s := by simp [hb]
 cocycle s t r := by
  simp [map_mul, map_inv, MulAut.mul_apply, mul_assoc, mul_left_comm, mul_comm]

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology

def xorList : List ℕ → ℕ
 | [] => 0
 | a :: as => a ^^^ xorList as

lemma ev_xorList {n : ℕ} (x : Fin n → ZMod 2) (rs : List ℕ) :
    ev x (xorList rs) = (rs.map (ev x)).sum := by
  induction rs with
  | nil => exact ev_zero x
  | cons a as ih => simp only [xorList, ev_xor, ih, List.map_cons, List.sum_cons]

structure Step where
  source : ℕ
  mask : ℕ
  parents : List ℕ
  deriving Inhabited

/-- A finite prefix of a row table, with an implementation-independent lookup. -/
structure StepTable where
  size : ℕ
  get : ℕ → Step

def row (ss : StepTable) (k : ℕ) : ℕ := (ss.get k).mask

def Valid (ss : StepTable) (raw : ℕ → ℕ) : Prop :=
  ∀ k : Fin ss.size, (∀ j ∈ (ss.get k.val).parents, j < k.val) ∧
    row ss k.val = raw (ss.get k.val).source ^^^ xorList ((ss.get k.val).parents.map (row ss))

lemma rows_zero {n : ℕ} (x : Fin n → ZMod 2) (ss : StepTable) (raw : ℕ → ℕ)
    (hv : Valid ss raw) (hr : ∀ k, ev x (raw k) = 0) :
    ∀ k, k < ss.size → ev x (row ss k) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    obtain ⟨hp, he⟩ := hv ⟨k, hk⟩
    rw [he, ev_xor, hr, zero_add, ev_xorList, List.map_map]
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    exact ih j (hp j hj) ((hp j hj).trans hk)

def Covers {n : ℕ} (ss : StepTable) (piv : Fin n → ℕ) : Prop :=
  ∀ p, piv p ≠ 0 → piv p - 1 < ss.size ∧
    row ss (piv p - 1) < 2 ^ (p.val + 1) ∧
    (row ss (piv p - 1)).testBit p.val = true

lemma kernel_zero {n : ℕ} (x : Fin n → ZMod 2) (ss : StepTable) (raw : ℕ → ℕ)
    (hv : Valid ss raw) (hr : ∀ k, ev x (raw k) = 0)
    (piv : Fin n → ℕ) (hc : Covers ss piv)
    (hf : ∀ p, piv p = 0 → x p = 0) : x = 0 := by
  have hrz := rows_zero x ss raw hv hr
  have hx : ∀ k, ∀ hk : k < n, x ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hp : piv ⟨k, hk⟩ = 0
      · exact hf ⟨k, hk⟩ hp
      · obtain ⟨hi, hlt, hbit⟩ := hc ⟨k, hk⟩ hp
        rw [← ev_top x ⟨k, hk⟩ _ hlt hbit]
        · exact hrz _ hi
        · intro j hj
          exact ih j.val hj j.isLt
  funext p
  exact hx p.val p.isLt
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
lemma ev_add {n : ℕ} (x y : Fin n → ZMod 2) (r : ℕ) :
    ev (x + y) r = ev x r + ev y r := by
  simp only [ev, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
lemma binary_inv (v : BinaryFour) : v⁻¹ = v := by
  change -v.toAdd = v.toAdd
  funext i
  exact CharTwo.neg_eq _

lemma binary_mul_self (v : BinaryFour) : v * v = 1 := by
  change v.toAdd + v.toAdd = 0
  funext i
  exact CharTwo.add_self_eq_zero _
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
