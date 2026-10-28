module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic


/-!
# Sound balanced radix conversion for the expansion certificates

A row's first n bits are split into low and high halves and converted to
base 4096. The proved splitting identity allows zero subblocks to be skipped.
The original `Wide.checkSpread` accepts this conversion, including all n
digits and the zero remainder. Thus list conversion certificates imply the
literal `Wide.checkSpreadRows` obligations used by the right singular expression.

This adapts the project's base-2048 argument in
`NativeActions/Relations1792/GeneratorOrders/Checker.lean` to the exact
base-4096 convention here. No external code is ported. See `source/README.md`.
-/

@[expose] public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.ExpansionChecks

/-- Sequential conversion used only at the leaves of the balanced algorithm. -/
def expand : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x => x % 2 + 4096 * expand n (x / 2)

theorem expand_zero (n : Nat) : expand n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expand, ih]

theorem expand_mod (n a : Nat) : expand n (a % 2^n) = expand n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [expand, pow_succ']
    rw [Nat.mod_mul_right_div_self, ih, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 (2^n))]

theorem expand_add (m n a : Nat) :
    expand (m+n) a = expand m a + 4096 ^ m * expand n (a / 2 ^ m) := by
  induction m generalizing a with
  | zero => simp [expand]
  | succ m ih =>
    simp only [Nat.succ_add, expand, ih, pow_succ', Nat.div_div_eq_div_mul]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- Split at the middle bit, omitting only subblocks proved to be zero. -/
def expandTree : Nat → Nat → Nat → Nat
  | 0, n, a => expand n a
  | k+1, n, a => if a == 0 then 0 else
      let m := n / 2
      expandTree k m (a % 2^m) + 4096^m * expandTree k (n-m) (a / 2^m)

theorem expandTree_eq (k n a : Nat) : expandTree k n a = expand n a := by
  induction k generalizing n a with
  | zero => rfl
  | succ k ih =>
    simp only [expandTree]
    split
    · next h =>
        have ha : a = 0 := by simpa only [beq_iff_eq] using h
        rw [ha, expand_zero]
    · rw [ih, ih, expand_mod, ← expand_add]
      congr 1
      omega

/-- The original checker accepts every digit of the computed expansion,
including the terminal zero above the stated dimension. -/
theorem checkSpread_expand (n x : Nat) : Wide.checkSpread n x (expand n x) = true := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h : x % 2 < 4096 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    simp only [expand, Wide.checkSpread, Bool.and_eq_true, beq_iff_eq]
    constructor
    · simp [Nat.add_mod, Nat.mod_eq_of_lt h]
    · rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h, Nat.zero_add]
      exact ih _

theorem checkSpreadRows_of_tree (k n : Nat) (a w : List Nat)
    (h : w = a.map (expandTree k n)) : Wide.checkSpreadRows n a w = true := by
  rw [h]
  clear h w
  induction a with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.map_cons, Wide.checkSpreadRows, expandTree_eq,
      checkSpread_expand, Bool.true_and] using ih

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.ExpansionChecks
