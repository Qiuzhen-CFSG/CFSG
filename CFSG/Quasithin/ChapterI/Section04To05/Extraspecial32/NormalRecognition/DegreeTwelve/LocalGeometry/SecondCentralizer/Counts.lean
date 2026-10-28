module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.ModelTypes
import Mathlib.Tactic.Tauto

/-!
# The two mixed-pair counts in the marked symmetric models

The certificates enumerate the actual products `C₂ × S₄` and `C₂ × S₅`.
A short candidate order is checked against every positive smaller power, so
it agrees with `orderOf`. Filtering the two ambient class predicates and the
canonical half-order equation then gives exactly 3 and 195 pairs.

All finite checks use kernel reduction. The counting sets first filter the
involution classes before forming their product. No Mathieu order, simplicity,
internal conjugacy-class identification, or external computation is assumed.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.2–4.3. The degree-five count is computed directly
in the symmetric model instead of comparing with a Mathieu realization.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Theory.GroupTheory.TwoInvolutionClassOrder

private def candidateOrder {n : ℕ} (x : Model n) : ℕ :=
  if x = 1 then 1 else if x ^ 2 = 1 then 2 else
  if x ^ 3 = 1 then 3 else if x ^ 4 = 1 then 4 else
  if x ^ 5 = 1 then 5 else if x ^ 6 = 1 then 6 else 10

private theorem candidateOrder_pos {n : ℕ} (x : Model n) :
    0 < candidateOrder x := by
  unfold candidateOrder
  split_ifs <;> decide

private def firstSet (n : ℕ) : Finset (Model n) :=
  Finset.univ.filter (fun x => x ^ 2 = 1 ∧ x ≠ 1 ∧ x.1 = 1 ∧ Equiv.Perm.sign x.2 = 1)
private def secondSet (n : ℕ) : Finset (Model n) :=
  Finset.univ.filter (fun x => x ^ 2 = 1 ∧ x ≠ 1 ∧
    ¬ (x.1 = 1 ∧ Equiv.Perm.sign x.2 = 1))
private def pairs (n : ℕ) : Finset (Model n × Model n) :=
  ((firstSet n).product (secondSet n)).filter
    (fun p => (p.1 * p.2) ^ (candidateOrder (p.1 * p.2) / 2) = centralInvolution n)

private theorem mem_firstSet {n : ℕ} (x : Model n) :
    x ∈ firstSet n ↔ FirstClass x := by
  simp [firstSet, FirstClass, orderOf_eq_prime_iff, and_assoc]

private theorem mem_secondSet {n : ℕ} (x : Model n) :
    x ∈ secondSet n ↔ SecondClass x := by
  simp only [secondSet, Finset.mem_filter, Finset.mem_univ, true_and,
    SecondClass, FirstClass, orderOf_eq_prime_iff]
  tauto

private theorem orderOf_eq_candidate {n : ℕ}
    (h : ∀ x : Model n, x ^ candidateOrder x = 1 ∧
      ∀ k ∈ Finset.Ico 1 (candidateOrder x), x ^ k ≠ 1) (x : Model n) :
    orderOf x = candidateOrder x := by
  apply (orderOf_eq_iff (candidateOrder_pos x)).mpr
  exact ⟨(h x).1, fun k hk hkpos => (h x).2 k (Finset.mem_Ico.mpr ⟨hkpos, hk⟩)⟩

private theorem card_modelFiber {n : ℕ}
    (h : ∀ x : Model n, x ^ candidateOrder x = 1 ∧
      ∀ k ∈ Finset.Ico 1 (candidateOrder x), x ^ k ≠ 1) :
    Nat.card (ModelFiber n) = (pairs n).card := by
  have e : ModelFiber n ≃ (pairs n) := Equiv.subtypeEquivRight (fun p => by
    simp only [pairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      mem_firstSet, mem_secondSet,
      halfOrder_def, orderOf_eq_candidate h]
    tauto)
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

set_option maxRecDepth 4096 in
private theorem orders_four : ∀ x : Model 4, x ^ candidateOrder x = 1 ∧
    ∀ k ∈ Finset.Ico 1 (candidateOrder x), x ^ k ≠ 1 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem count_four : (pairs 4).card = 3 := by decide +kernel

/-- The first centralizer alternative has exactly three mixed pairs. -/
public theorem card_modelFiber_four : Nat.card (ModelFiber 4) = 3 :=
  (card_modelFiber orders_four).trans count_four

set_option maxRecDepth 4096 in
private theorem orders_five : ∀ x : Model 5, x ^ candidateOrder x = 1 ∧
    ∀ k ∈ Finset.Ico 1 (candidateOrder x), x ^ k ≠ 1 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem count_five : (pairs 5).card = 195 := by decide +kernel

/-- The second centralizer alternative has exactly 195 mixed pairs. -/
public theorem card_modelFiber_five : Nat.card (ModelFiber 5) = 195 :=
  (card_modelFiber orders_five).trans count_five

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
