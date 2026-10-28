module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Checks

/-!
# Indexed evaluation of the commutant certificates

The original `scan` successively shifts its mask and XORs a zero for every
unselected row. Here the mask is fixed, the bit index increases, and only
selected rows change the accumulator. Induction proves exact agreement with
`scan`; no finite arithmetic is trusted. The concrete consumer is the pivot
and upper-entry certification in `Elimination`.

Source: `Commutant/source/README.md` and `Commutant/Arithmetic.lean`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof.Elimination

def fastScan (x : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | i, y :: ys, acc => fastScan x (i+1) ys (if x.testBit i then acc ^^^ y else acc)

theorem fastScan_eq (x i acc : ℕ) (ys : List ℕ) :
    fastScan x i ys acc = acc ^^^ scan (x >>> i) ys := by
  induction ys generalizing i acc with
  | nil => simp [fastScan, scan]
  | cons y ys ih =>
    simp only [fastScan, scan, ih, Nat.testBit_shiftRight, ← Nat.shiftRight_add]
    split <;> simp_all [Nat.xor_assoc]

theorem scan_eq_fast (x : ℕ) (ys : List ℕ) :
    scan x ys = fastScan x 0 ys 0 := by
  simpa using (fastScan_eq x 0 0 ys).symm
end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof.Elimination
