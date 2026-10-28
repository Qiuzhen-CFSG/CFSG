module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates

/-!
# Splitting binary displacement into two small tables

XOR-linearity of the literal eleven-row `maskImage` reduces fixedness to equality
of the displacements of the high five bits and low six bits. Thus the concrete
checker only needs 32 + 64 row evaluations for each actor.
The direct action and basis convention are those of `Image.StarData`.
-/
@[expose] public section
open Janko4.Cardinality.QuotientCount.Image
namespace Janko4.TwoRank.Finite
private lemma xor_left_comm (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]
@[simp] private lemma xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
lemma maskImage_xor (rs : Fin 11 → ℕ) (m n : ℕ) :
    maskImage rs (m ^^^ n) = maskImage rs m ^^^ maskImage rs n := by
  have h (l : List (Fin 11)) :
      (l.map (fun i => if (m ^^^ n).testBit i.val then rs i else 0)).foldr Nat.xor 0 =
      (l.map (fun i => if m.testBit i.val then rs i else 0)).foldr Nat.xor 0 ^^^
      (l.map (fun i => if n.testBit i.val then rs i else 0)).foldr Nat.xor 0 := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      simp only [Nat.testBit_xor]
      cases hm : m.testBit i.val <;> cases hn : n.testBit i.val <;>
        simp [Nat.xor_assoc, xor_left_comm]
  simpa only [List.map_ofFn, Function.comp_def, maskImage] using h (List.ofFn (fun i : Fin 11 => i))
private lemma xor_balance (a b c d : ℕ) (h : a ^^^ b = c ^^^ d) : a ^^^ c = b ^^^ d := by
  have := congrArg (fun x => x ^^^ (b ^^^ c)) h
  simpa [Nat.xor_assoc, Nat.xor_comm, xor_left_comm] using this

private theorem packed_xor (a : Fin 32) (b : Fin 64) :
    a.val * 64 + b.val = (a.val * 64) ^^^ b.val := by
  have h : ∀ (a : Fin 32) (b : Fin 64),
      a.val * 64 + b.val = (a.val * 64) ^^^ b.val := by decide +kernel
  exact h a b

/-- Fixedness equates the displacements of the two disjoint pieces. -/
theorem displacement_eq (rs : Fin 11 → ℕ) (a : Fin 32) (b : Fin 64)
    (h : maskImage rs (a.val * 64 + b.val) = a.val * 64 + b.val) :
    maskImage rs (a.val * 64) ^^^ (a.val * 64) = maskImage rs b.val ^^^ b.val := by
  rw [packed_xor, maskImage_xor] at h
  exact xor_balance _ _ _ _ h
end Janko4.TwoRank.Finite
