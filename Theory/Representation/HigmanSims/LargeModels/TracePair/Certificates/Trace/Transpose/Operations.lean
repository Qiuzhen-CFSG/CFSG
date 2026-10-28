module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed

/-!
# Bit routing and rectangular packed blocks

A list of shift-and-mask stages routes individual bits. `testBit_permute`
proves its semantics using the explicit list of source addresses. `pack`
concatenates consecutive 128-bit row fragments, and `testBit_pack` identifies
the original row and column of each bit. Together these lemmas support bounded
transpose certificates without repeatedly traversing all 896 rows.

The consumer is the literal ATLAS HS generator; see `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose

/-- Materialize an arithmetic state before the three mask operations reuse it.
The body is exposed because the downstream certificates reduce `permute`. -/
def forceNat {α : Sort*} (n : ℕ) (f : ℕ → α) : α :=
  match n with | 0 => f 0 | n + 1 => f (n + 1)

def pack (w : ℕ) (p : Packed.Row → ℕ) (k : ℕ) : Packed.Mat → ℕ
  | [] => 0
  | r :: rs => ((p r >>> k) % 2 ^ w) ||| (pack w p k rs <<< w)

def permute : List (ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], x => x
  | (d, lo, hi, stay) :: ss, x => forceNat (permute ss x) fun y =>
      (y &&& stay) ||| ((y >>> d) &&& lo) ||| ((y <<< d) &&& hi)

def route : List (ℕ × ℕ × ℕ × ℕ) → ℕ → List ℕ
  | [], i => [i]
  | (d, lo, hi, stay) :: ss, i =>
      (if stay.testBit i then route ss i else []) ++
      (if lo.testBit i then route ss (d + i) else []) ++
      (if hi.testBit i && decide (d ≤ i) then route ss (i - d) else [])

private theorem forceNat_eq {α : Sort*} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

theorem testBit_permute (ss : List (ℕ × ℕ × ℕ × ℕ)) (x i : ℕ) :
    (permute ss x).testBit i = (route ss i).any x.testBit := by
  induction ss generalizing i with
  | nil => simp [permute, route]
  | cons sm ss ih =>
    rcases sm with ⟨d, lo, hi, stay⟩
    simp only [permute, forceNat_eq, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ih, route, List.any_append]
    cases stay.testBit i <;> cases lo.testBit i <;> cases hi.testBit i <;>
      by_cases h : d ≤ i <;> simp [h, Bool.and_comm]

theorem testBit_pack (p : Packed.Row → ℕ) (hp : p (0, 0) = 0)
    (a : Packed.Mat) (k i j : ℕ) (hj : j < 128) :
    (pack 128 p k a).testBit (128 * i + j) =
      (p (a.getD i (0, 0))).testBit (k + j) := by
  induction a generalizing i with
  | nil => simp [pack, hp]
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [pack, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, Nat.testBit_or,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        hj, decide_true, Nat.not_le.mpr hj, decide_false, Bool.false_and,
        Bool.or_false, Bool.true_and]
    | succ i =>
      have hge : 128 ≤ 128 * (i + 1) + j := by omega
      have heq : 128 * (i + 1) + j - 128 = 128 * i + j := by omega
      simp only [pack, Nat.testBit_or, Nat.testBit_mod_two_pow,
        Nat.testBit_shiftLeft, hge, decide_true, Nat.not_lt.mpr hge,
        decide_false, Bool.false_and, Bool.false_or, Bool.true_and, heq,
        List.getD_cons_succ]
      exact ih i

theorem getD_block (a : Packed.Mat) (k i : ℕ) (hi : i < 128) :
    ((a.drop k).take 128).getD i (0, 0) = a.getD (k + i) (0, 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true, List.getElem?_drop]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose
