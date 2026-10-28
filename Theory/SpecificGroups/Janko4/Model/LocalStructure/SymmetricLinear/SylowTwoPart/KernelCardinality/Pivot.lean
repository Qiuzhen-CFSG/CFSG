module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-!
# Pivot for the max4 binary-product certificate

Ordered binary products are distinct when each word has a new pivot. A row-prefix condition makes the pivot entry additive on each remaining suffix; cancelling the common first factor gives induction.

The concrete consumer is `KernelCardinality.lean`; matrix and word sources
are the ATLAS representation and J4G1-max4W1, attributed in Model.Data and
SymmetricLinear.Model. See SylowTwoPart/source/README.md.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.OrderedBinaryProducts
variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 2)
structure RowPrefix (r : Fin n) (A : Mat n) : Prop where
  before : ∀ i, i < r → ∀ j, A i j = (1 : Mat n) i j
  diagonal : A r r = 1
  above : ∀ j, r < j → A r j = 0

lemma prefix_one (r : Fin n) : RowPrefix r (1 : Mat n) := by
  constructor
  · intros; rfl
  · simp
  · intro j hj; simp [ne_of_lt hj]

lemma prefix_mul {r : Fin n} {A B : Mat n} (hA : RowPrefix r A)
    (hB : RowPrefix r B) : RowPrefix r (A * B) := by
  constructor
  · intro i hi j
    simp only [Matrix.mul_apply, hA.before i hi]
    change ((1 : Mat n) * B) i j = _
    rw [one_mul, hB.before i hi]
  · rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · rw [hA.diagonal, hB.diagonal, one_mul]
    · intro k _ hkr
      rcases lt_or_gt_of_ne hkr with hk | hk
      · rw [hB.before k hk, Matrix.one_apply_ne hkr, mul_zero]
      · rw [hA.above k hk, zero_mul]
    · simp
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · rw [hB.above j hj, mul_zero]
    · intro k _ hkr
      rcases lt_or_gt_of_ne hkr with hk | hk
      · rw [hB.before k hk, Matrix.one_apply_ne (ne_of_lt (hk.trans hj)), mul_zero]
      · rw [hA.above k hk, zero_mul]
    · simp

lemma pivot_mul {r c : Fin n} (hc : c < r) {A B : Mat n}
    (hA : RowPrefix r A) (hB : RowPrefix r B) :
    (A * B) r c = A r c + B r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem r c (Finset.mem_univ _) (Finset.mem_univ _)
    (ne_of_gt hc)]
  · rw [hA.diagonal, hB.before c hc, Matrix.one_apply_eq, one_mul, mul_one, add_comm]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk.1 with hkr | hkr
    · rw [hB.before k hkr, Matrix.one_apply_ne hk.2, mul_zero]
    · rw [hA.above k hkr, zero_mul]

variable {G : Type*} [Group G] (f : G →* Mat n)
lemma prod_zero (r c : Fin n) (hc : c < r) (L : List G)
    (h : ∀ g ∈ L, RowPrefix r (f g) ∧ f g r c = 0) :
    RowPrefix r (f L.prod) ∧ f L.prod r c = 0 := by
  induction L with
  | nil => simp only [List.prod_nil, map_one]; exact ⟨prefix_one r, Matrix.one_apply_ne (ne_of_gt hc)⟩
  | cons g L ih =>
    obtain ⟨hg, hg0⟩ := h g (by simp)
    obtain ⟨hL, hL0⟩ := ih (fun g hg => h g (by simp [hg]))
    rw [List.prod_cons, map_mul]
    exact ⟨prefix_mul hg hL, by rw [pivot_mul hc hg hL, hg0, hL0, add_zero]⟩

lemma binary_injective (m : ℕ) (w : Fin m → G) (r c : Fin m → Fin n)
    (hc : ∀ i, c i < r i)
    (hp : ∀ i j, i ≤ j → RowPrefix (r i) (f (w j)))
    (hv : ∀ i, f (w i) (r i) (c i) = 1)
    (hz : ∀ i j, i < j → f (w j) (r i) (c i) = 0) :
    Function.Injective (fun b : Fin m → Fin 2 => (List.ofFn (fun i => w i ^ (b i).val)).prod) := by
  induction m with
  | zero => intro a b _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro a b hab
    simp only [List.ofFn_succ, List.prod_cons] at hab
    have tail_zero (d : Fin (m+1) → Fin 2) :
        RowPrefix (r 0) (f ((List.ofFn (fun i : Fin m => w i.succ ^ (d i.succ).val)).prod)) ∧
        f ((List.ofFn (fun i : Fin m => w i.succ ^ (d i.succ).val)).prod) (r 0) (c 0) = 0 := by
      apply prod_zero f _ _ (hc 0)
      intro g hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      have hpre := hp 0 j.succ (Fin.zero_le _)
      have hzero := hz 0 j.succ (Fin.succ_pos _)
      generalize d j.succ = bit
      fin_cases bit <;> simp only [pow_zero, pow_one, map_one]
      · exact ⟨prefix_one _, Matrix.one_apply_ne (ne_of_gt (hc 0))⟩
      · exact ⟨hpre, hzero⟩
    have detect (d : Fin (m+1) → Fin 2) :
        f (w 0 ^ (d 0).val * (List.ofFn (fun i : Fin m => w i.succ ^ (d i.succ).val)).prod)
          (r 0) (c 0) = (d 0).val := by
      obtain ⟨ht, ht0⟩ := tail_zero d
      rw [map_mul]
      generalize hd : d 0 = bit
      fin_cases bit
      · simpa using ht0
      · simp only [pow_one]
        rw [pivot_mul (hc 0) (hp 0 0 le_rfl) ht, hv 0, ht0, add_zero]
        rfl
    have hbit : a 0 = b 0 := by
      have he := congrArg (fun g => f g (r 0) (c 0)) hab
      rw [detect a, detect b] at he
      apply Fin.ext
      have he' := congrArg ZMod.val he
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (a 0).isLt,
        Nat.mod_eq_of_lt (b 0).isLt] using he'
    rw [hbit] at hab
    have htail := mul_left_cancel hab
    have he := ih (fun i => w i.succ) (fun i => r i.succ) (fun i => c i.succ)
      (fun i => hc i.succ) (fun i j hij => hp i.succ j.succ (by simpa using hij))
      (fun i => hv i.succ) (fun i j hij => hz i.succ j.succ (by simpa using hij)) htail
    funext i
    refine Fin.cases hbit (fun j => congrFun he j) i
end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.OrderedBinaryProducts
