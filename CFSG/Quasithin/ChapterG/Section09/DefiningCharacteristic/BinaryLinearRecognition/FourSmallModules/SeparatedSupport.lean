module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.RootDifferences
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Separated endpoint support in binary SL₄

A nonzero local highest vector with support `{0, 2}` has eleven independent
permutation translates. Each coefficient extractor is a product of at most
two transvection differences. It kills the earlier translates and sends its
own translate to a nonzero permutation translate. The action identities use
only upper fixedness, the inactive middle exchange, and the active endpoint
relations; neither faithfulness nor irreducibility is required.

The extraction argument adapts the binary SL₅ `Separated.Extraction` proof in
this repository. The certificate here uses only the four actual coordinates;
its eleven translates correspond to all ordered pairs of distinct coordinates
except `(3, 0)`.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357/PDF pp.365,367--368. The bound eleven
suffices to exclude this support at cutoff ten; no degree-gap theorem is used.
-/

@[expose] public section

open Representation
open scoped MatrixGroups BigOperators

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace SeparatedSupport

private def swapWord (w : List (Fin 3)) : Group := (w.map simpleSwap).prod

private def rootElement (a b : Fin 4) : Group :=
  if hab : a ≠ b then Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2) else 1

private def difference {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (t : Group) : V →ₗ[ZMod 2] V :=
  ρ t - LinearMap.id

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma fixed_word {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (w : List (Fin 3)) (hw : ∀ i ∈ w, i ∉ J) :
    ρ (swapWord w) v = v := by
  induction w with
  | nil => simp [swapWord]
  | cons i w ih =>
    change ρ (simpleSwap i * swapWord w) v = v
    rw [map_mul]
    change ρ (simpleSwap i) (ρ (swapWord w) v) = v
    rw [ih (fun j hj => hw j (by simp [hj]))]
    exact h.inactive_fixed i (hw i (by simp))

private lemma apply_mul (ρ : Representation (ZMod 2) Group V) (a b : Group) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl

private lemma difference_zero {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (t a : Group) (q : List (Fin 3))
    (hq : ∀ i ∈ q, i ∉ J) (r s : Fin 4) (hrs : r < s)
    (he : t * a * swapWord q = a * swapWord q * rootElement r s) :
    difference ρ t (ρ a v) = 0 := by
  have hu : ρ (rootElement r s) v = v := by
    simpa [rootElement, ne_of_lt hrs] using h.upper_fixed r s hrs
  have hh := congrArg (fun g => ρ g v) he
  simp only [apply_mul, fixed_word h q hq, hu] at hh
  change ρ t (ρ a v) - ρ a v = 0
  exact sub_eq_zero.mpr hh

private lemma lower_apply {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (i : Fin 3) (hi : i ∈ J) :
    ρ (simpleLower i) v = v + ρ (simpleSwap i) v := by
  have binary (x : V) : x + x = 0 := by
    have hh : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh
  have hh := congrArg (fun x => x + ρ (simpleLower i) v) (h.active_relation i hi)
  simpa only [add_assoc, binary, add_zero, zero_add] using hh.symm

private lemma difference_step {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector ρ J v) (t a b : Group) (q r : List (Fin 3))
    (hq : ∀ i ∈ q, i ∉ J) (hr : ∀ i ∈ r, i ∉ J)
    (i : Fin 3) (hi : i ∈ J)
    (he : t * a * swapWord q = a * swapWord q * simpleLower i)
    (hf : a * swapWord q * simpleSwap i = b * swapWord r) :
    difference ρ t (ρ a v) = ρ b v := by
  have hh := congrArg (fun g => ρ g v) he
  have hk := congrArg (fun g => ρ g v) hf
  simp only [apply_mul, fixed_word h r hr] at hk
  simp only [apply_mul, fixed_word h q hq, lower_apply h i hi, map_add, hk] at hh
  change ρ t (ρ a v) - ρ a v = ρ b v
  rw [hh, add_sub_cancel_left]

private lemma translate_ne_zero (ρ : Representation (ZMod 2) Group V) (a : Group)
    {v : V} (hv : v ≠ 0) : ρ a v ≠ 0 := by
  intro he
  have hh := congrArg (ρ a⁻¹) he
  rw [← apply_mul, inv_mul_cancel, map_one] at hh
  exact hv (by simpa using hh)

/-- Linear endomorphisms separating each vector from its predecessors certify independence. -/
private theorem linearIndependent_of_triangular {n : ℕ} (f : Fin n → V)
    (D : Fin n → V →ₗ[ZMod 2] V)
    (hzero : ∀ i j, j < i → D i (f j) = 0)
    (hne : ∀ i, D i (f i) ≠ 0) : LinearIndependent (ZMod 2) f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := ⟨j, by simp [s, hj]⟩
  let i := s.max' hs
  have hi : c i ≠ 0 := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have he := congrArg (D i) hc
  simp only [map_sum, map_smul, map_zero] at he
  have hh : ∑ k, c k • D i (f k) = c i • D i (f i) := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases hlt : k < i
      · rw [hzero i k hlt, smul_zero]
      · have hk : c k = 0 := by
          by_contra hk
          have hle : k ≤ i := s.le_max' k (by simp [s, hk])
          exact hki (le_antisymm hle (le_of_not_gt hlt))
        rw [hk, zero_smul]
    · simp
  rw [hh] at he
  exact (smul_ne_zero hi (hne i)) he

variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {0, 2} v)
include h

-- The endpoint images `(w(0), w(3))`, in this order, are
-- `(0,3), (1,3), (0,2), (2,3), (1,2), (0,1), (3,2), (2,1), (1,0), (3,1), (2,0)`.
-- The inactive middle exchange allows either ordering of the two other coordinates.
private def w0 : Group := swapWord []
private def w1 : Group := swapWord [0]
private def w2 : Group := swapWord [2]
private def w3 : Group := swapWord [1, 0]
private def w4 : Group := swapWord [2, 0]
private def w5 : Group := swapWord [1, 2]
private def w6 : Group := swapWord [2, 1, 0]
private def w7 : Group := swapWord [1, 2, 0]
private def w8 : Group := swapWord [0, 1, 2]
private def w9 : Group := swapWord [1, 2, 1, 0]
private def w10 : Group := swapWord [0, 1, 2, 0]

private theorem action0 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide) 0 1 (by decide)
  decide

private theorem action1 : difference ρ (rootElement 0 1) (ρ w1 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 1) w1 w0
    [] [] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action2 : difference ρ (rootElement 2 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w0
    [] (by decide) 2 3 (by decide)
  decide

private theorem action3 : difference ρ (rootElement 2 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w1
    [] (by decide) 2 3 (by decide)
  decide

private theorem action4 : difference ρ (rootElement 2 3) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 3) w2 w0
    [] [] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action5 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by decide) 0 2 (by decide)
  decide

private theorem action6 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide) 1 2 (by decide)
  decide

private theorem action7 : difference ρ (rootElement 0 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w2
    [] (by decide) 0 3 (by decide)
  decide

private theorem action8 : difference ρ (rootElement 0 2) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 2) w3 w0
    [] [1] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action9 : difference ρ (rootElement 2 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w0
    [1] (by decide) 1 2 (by decide)
  decide

private theorem action10 : difference ρ (rootElement 0 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide) 0 1 (by decide)
  decide

private theorem action11 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide) 1 2 (by decide)
  decide

private theorem action12 : difference ρ (rootElement 0 1) (ρ w4 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 1) w4 w2
    [] [] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action13 : difference ρ (rootElement 2 1) (ρ w2 v) = ρ w5 v := by
  apply difference_step h (rootElement 2 1) w2 w5
    [1] [1] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action14 : difference ρ (rootElement 1 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w0
    [] (by decide) 1 3 (by decide)
  decide

private theorem action15 : difference ρ (rootElement 1 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w1
    [] (by decide) 0 3 (by decide)
  decide

private theorem action16 : difference ρ (rootElement 1 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by decide) 1 2 (by decide)
  decide

private theorem action17 : difference ρ (rootElement 1 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w3
    [] (by decide) 2 3 (by decide)
  decide

private theorem action18 : difference ρ (rootElement 1 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w4
    [] (by decide) 0 2 (by decide)
  decide

private theorem action19 : difference ρ (rootElement 1 3) (ρ w5 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 3) w5 w0
    [] [1] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action20 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by decide) 0 3 (by decide)
  decide

private theorem action21 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide) 1 3 (by decide)
  decide

private theorem action22 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by decide) 0 2 (by decide)
  decide

private theorem action23 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by decide) 1 3 (by decide)
  decide

private theorem action24 : difference ρ (rootElement 0 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w4
    [] (by decide) 1 2 (by decide)
  decide

private theorem action25 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by decide) 0 2 (by decide)
  decide

private theorem action26 : difference ρ (rootElement 0 3) (ρ w6 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 3) w6 w2
    [] [1] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action27 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by decide) 1 2 (by decide)
  decide

private theorem action28 : difference ρ (rootElement 0 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w4
    [] (by decide) 1 3 (by decide)
  decide

private theorem action29 : difference ρ (rootElement 0 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide) 0 1 (by decide)
  decide

private theorem action30 : difference ρ (rootElement 0 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w6
    [] (by decide) 1 3 (by decide)
  decide

private theorem action31 : difference ρ (rootElement 0 2) (ρ w7 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 2) w7 w5
    [] [] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action32 : difference ρ (rootElement 1 2) (ρ w5 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 2) w5 w2
    [1] [1] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action33 : difference ρ (rootElement 0 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w5
    [] (by decide) 0 3 (by decide)
  decide

private theorem action34 : difference ρ (rootElement 0 2) (ρ w8 v) = ρ w4 v := by
  apply difference_step h (rootElement 0 2) w8 w4
    [1] [1] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action35 : difference ρ (rootElement 1 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w2
    [] (by decide) 1 3 (by decide)
  decide

private theorem action36 : difference ρ (rootElement 0 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w7
    [] (by decide) 1 2 (by decide)
  decide

private theorem action37 : difference ρ (rootElement 0 3) (ρ w8 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 3) w8 w1
    [] [1] (by decide) (by decide) 2 (by decide) <;> decide

private theorem action38 : difference ρ (rootElement 1 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w1
    [] (by decide) 0 2 (by decide)
  decide

private theorem action39 : difference ρ (rootElement 0 3) (ρ w9 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 3) w9 w5
    [] [1] (by decide) (by decide) 0 (by decide) <;> decide

private theorem action40 : difference ρ (rootElement 0 3) (ρ w10 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 3) w10 w3
    [] [1] (by decide) (by decide) 2 (by decide) <;> decide

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 11 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 11 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 2 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp (LinearMap.id),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 1)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id))]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
      rw [action0 h]
    · change difference ρ (rootElement 2 3) (ρ w0 v) = 0
      rw [action2 h]
    · change difference ρ (rootElement 2 3) (ρ w1 v) = 0
      rw [action3 h]
    · change difference ρ (rootElement 0 2) (ρ w0 v) = 0
      rw [action5 h]
    · change difference ρ (rootElement 0 2) (ρ w1 v) = 0
      rw [action6 h]
    · change difference ρ (rootElement 0 2) (ρ w2 v) = 0
      rw [action7 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
      rw [action0 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
      rw [action1 h, action9 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
      rw [action10 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
      rw [action11 h, map_zero]
    · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
      rw [action14 h]
    · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
      rw [action15 h]
    · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
      rw [action16 h]
    · change difference ρ (rootElement 1 3) (ρ w3 v) = 0
      rw [action17 h]
    · change difference ρ (rootElement 1 3) (ρ w4 v) = 0
      rw [action18 h]
    · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
      rw [action20 h]
    · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
      rw [action21 h]
    · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
      rw [action22 h]
    · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
      rw [action23 h]
    · change difference ρ (rootElement 0 3) (ρ w4 v) = 0
      rw [action24 h]
    · change difference ρ (rootElement 0 3) (ρ w5 v) = 0
      rw [action25 h]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
      rw [action5 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
      rw [action6 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
      rw [action7 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
      rw [action8 h, action27 h]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
      rw [action29 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
      rw [action30 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
      rw [action5 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
      rw [action6 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
      rw [action7 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
      rw [action8 h, action0 h]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
      rw [action29 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
      rw [action30 h, map_zero]
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w7 v)) = 0
      rw [action31 h, action33 h]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
      rw [action20 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
      rw [action21 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
      rw [action22 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
      rw [action23 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
      rw [action24 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
      rw [action25 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
      rw [action26 h, action35 h]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
      rw [action36 h, map_zero]
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
      rw [action37 h, action38 h]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
      rw [action20 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
      rw [action21 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
      rw [action22 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
      rw [action23 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
      rw [action24 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
      rw [action25 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
      rw [action26 h, action7 h]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
      rw [action36 h, map_zero]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
      rw [action37 h, action6 h]
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
      rw [action39 h, action29 h]
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w4 v)) ≠ 0
      rw [action12 h, action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w5 v) ≠ 0
      rw [action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w6 v) ≠ 0
      rw [action26 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w7 v)) ≠ 0
      rw [action31 h, action32 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 0 2) (ρ w8 v)) ≠ 0
      rw [action34 h, action12 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 3) (ρ w9 v)) ≠ 0
      rw [action39 h, action32 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w10 v)) ≠ 0
      rw [action40 h, action8 h]
      exact translate_ne_zero ρ _ hv

end SeparatedSupport

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A nonzero highest vector with the two endpoint roots active forces dimension
at least eleven, without faithfulness or irreducibility assumptions. -/
theorem LocalHighestVector.eleven_le_finrank_of_separated [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector ρ {0, 2} v) (hv : v ≠ 0) :
    11 ≤ Module.finrank (ZMod 2) V := by
  simpa using (SeparatedSupport.independent h hv).fintype_card_le_finrank

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
