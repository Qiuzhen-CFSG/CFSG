module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleEncoding
public import Mathlib.Data.Nat.Bits

/-!
# Bit-set disjointness certificates for finite cycle tables

The scanner records previously seen point labels in a natural-number bit set.
A successful scan certifies that the input list has no repetitions. This gives
a linear scan for the flattened ATLAS cycle tables without quadratic pairwise
comparison or reliance on private sorting implementations.
-/

@[expose] public section
namespace Sporadic.Fischer.AtlasCarriers

/-- Reject a repeated finite point, recording new points in a bit set. -/
def checkFreshPoints {n : Nat} : List (Fin n) → Nat → Bool
  | [], _ => true
  | x :: xs, seen =>
    if seen.testBit x.val then false else checkFreshPoints xs (seen ||| 2 ^ x.val)

private theorem checkFreshPoints_sound {n : Nat} (xs : List (Fin n)) (seen : Nat)
    (h : checkFreshPoints xs seen = true) :
    xs.Nodup ∧ ∀ x ∈ xs, seen.testBit x.val = false := by
  induction xs generalizing seen with
  | nil => simp
  | cons x xs ih =>
    cases hs : seen.testBit x.val with
    | true => simp [checkFreshPoints, hs] at h
    | false =>
      have hr := ih (seen ||| 2 ^ x.val) (by simpa only [checkFreshPoints, hs,
        Bool.false_eq_true, ↓reduceIte] using h)
      refine ⟨List.nodup_cons.mpr ⟨?_, hr.1⟩, ?_⟩
      · intro hx
        have hh := hr.2 x hx
        simp only [Nat.testBit_or, Nat.testBit_two_pow, decide_true, Bool.or_true] at hh
        contradiction
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hs
        · have hh := hr.2 y hy
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at hh
          exact hh.1

/-- Successful bit-set scanning proves that the finite labels are distinct. -/
theorem nodup_of_checkFreshPoints {n : Nat} (xs : List (Fin n))
    (h : checkFreshPoints xs 0 = true) : xs.Nodup :=
  (checkFreshPoints_sound xs 0 h).1

end Sporadic.Fischer.AtlasCarriers
