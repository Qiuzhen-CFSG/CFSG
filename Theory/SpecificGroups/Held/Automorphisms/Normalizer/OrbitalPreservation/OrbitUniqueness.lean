module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.OrbitTrees
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Bits

/-!
# The unique invariant subset of size 425

A set invariant under the point stabilizer has constant membership along
all five certified trees. The component sizes are 1, 425, 1360, 136, 136;
a finite check of their unions shows that only component 1 has size 425.
Reconstructing the binary row mask identifies this component with row zero
of the published relation. Neither graph invariance nor exact Held order
is assumed in this uniqueness result.

Source: the ATLAS forest in `Data`; this supplies the intrinsic-set part
of the full-normalizer argument supporting GLS3 Table 5.3p.
-/

namespace Held.NormalizerGraph.Orbital

private def pack (f : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => Nat.bit (f k) (pack f n (k + 1))

private theorem pack_testBit (f : ℕ → Bool) (n k i : ℕ) (hi : i < n) :
    (pack f n k).testBit i = f (k + i) := by
  induction n generalizing k i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp only [pack, Nat.testBit_bit_zero, Nat.add_zero]
    | succ i =>
      rw [pack, Nat.testBit_bit_succ, ih (k + 1) i (by omega)]
      congr 1
      omega

private def rowBits (i : ℕ) : Bool := color ⟨i % 2058, Nat.mod_lt _ (by decide)⟩ == 1

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem packed_row : pack rowBits 2058 0 = rowMask 0 := by decide +kernel

public theorem color_row (x : Fin 2058) : Adj 0 x ↔ color x = 1 := by
  have ht := pack_testBit rowBits 2058 0 x.val x.isLt
  rw [packed_row] at ht
  have he : (⟨(0 + x.val) % 2058, Nat.mod_lt _ (by decide)⟩ : Fin 2058) = x := by
    apply Fin.ext
    simpa only [Nat.zero_add] using Nat.mod_eq_of_lt x.isLt
  change (rowMask 0).testBit x.val = (color _ == 1) at ht
  rw [he] at ht
  simp only [Adj, ht, beq_iff_eq]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem count_unique : ∀ f : Fin 5 → Bool,
    (List.finRange 2058).countP (fun x => f (color x)) = 425 →
      ∀ c, f c = (c == 1) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem count_one : (List.finRange 2058).countP (fun x => color x == 1) = 425 := by
  decide +kernel

private theorem card_selected (f : Fin 5 → Bool) :
    Nat.card {x : Fin 2058 // f (color x) = true} =
      (List.finRange 2058).countP (fun x => f (color x)) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  simp only [Bool.decide_eq_true]

public theorem row_card : Nat.card {x : Fin 2058 // Adj 0 x} = 425 := by
  have he : {x : Fin 2058 // Adj 0 x} ≃ {x : Fin 2058 // (color x == 1) = true} :=
    Equiv.subtypeEquivRight (fun x => (color_row x).trans (by simp))
  exact (Nat.card_congr he).trans ((card_selected (fun c => c == 1)).trans count_one)

public theorem unique_invariant (p : Fin 2058 → Prop)
    (hp : ∀ g : Stabilizer, ∀ x, p (g • x) ↔ p x)
    (hc : Nat.card {x // p x} = 425) : ∀ x, p x ↔ Adj 0 x := by
  classical
  let f : Fin 5 → Bool := fun c => decide (p (rep c))
  have hpx (x : Fin 2058) : p x ↔ f (color x) = true := by
    obtain ⟨g, hg⟩ := reach x
    simpa only [f, decide_eq_true_eq, hg] using hp g (rep (color x))
  have he : {x // p x} ≃ {x : Fin 2058 // f (color x) = true} :=
    Equiv.subtypeEquivRight hpx
  rw [Nat.card_congr he, card_selected] at hc
  intro x
  rw [hpx, count_unique f hc, beq_iff_eq]
  exact (color_row x).symm


end Held.NormalizerGraph.Orbital
