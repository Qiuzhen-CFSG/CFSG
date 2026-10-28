module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles.Binary
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A fixed lower coordinate in central lifts of the J4 core matrices

The certified right-conjugation matrices of the actual max1 core have eleven
columns. A lift fixing an additional central coordinate is specified by 22
binary entries. Five quotient relators impose eleven independent equations.
The explicit mask certificate below expresses every generator entry as a
coboundary plus a combination of these equations. Thus the corrected lower
coordinate is invariant. No identification of the core with its dual is used.

All finite identities are reduced by Lean's kernel. The certificate works on
arbitrary lifted matrices; `Relations` supplies its group-word hypotheses for
an elementary preimage of the literal local core.

Source: ATLAS `J4G1-max1W1`, via `KernelCount.Tables` and the certified action
in `RelativeCocycles.Binary`; the module-cover interpretation is
Aschbacher–Smith I.1.5, printed p.408, and GLS3 Section 6.1.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement
open Cardinality.KernelCount
open Max1RelativeRigidity.RelativeCocycles (act actX actY)

abbrev V := BitVec 11

def evalRow {n : ℕ} (d : Fin n → Bool) (v : BitVec n) : Bool :=
  ∑ i, v.getLsbD i.val * d i

theorem evalRow_zero {n : ℕ} (d : Fin n → Bool) : evalRow d 0 = 0 := by
  simp [evalRow, Bool.mul_eq_and, Bool.zero_eq_false]

theorem evalRow_xor {n : ℕ} (d : Fin n → Bool) (v w : BitVec n) :
    evalRow d (v ^^^ w) = evalRow d v + evalRow d w := by
  simp only [evalRow, BitVec.getLsbD_xor, ← Bool.add_eq_xor, add_mul,
    Finset.sum_add_distrib]

def substitute {n m : ℕ} (rows : Fin n → BitVec m) (v : BitVec n) : BitVec m :=
  (List.ofFn (fun i => if v.getLsbD i.val then rows i else 0)).foldr (· ^^^ ·) 0

private theorem evalRow_fold {m : ℕ} (d : Fin m → Bool) (l : List (BitVec m)) :
    evalRow d (l.foldr (· ^^^ ·) 0) = (l.map (evalRow d)).sum := by
  induction l with
  | nil => exact evalRow_zero d
  | cons a l ih => simp only [List.foldr_cons, evalRow_xor, ih, List.map_cons, List.sum_cons]

theorem evalRow_substitute {n m : ℕ} (d : Fin m → Bool)
    (rows : Fin n → BitVec m) (v : BitVec n) :
    evalRow d (substitute rows v) = evalRow (fun i => evalRow d (rows i)) v := by
  rw [substitute, evalRow_fold, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  change evalRow d (if v.getLsbD i.val then rows i else 0) =
    v.getLsbD i.val * evalRow d (rows i)
  cases v.getLsbD i.val
  · change evalRow d 0 = 0 * evalRow d (rows i)
    rw [evalRow_zero, zero_mul]
  · change evalRow d (rows i) = 1 * evalRow d (rows i)
    rw [one_mul]

/-- Positive words act successively from left to right by right conjugation. -/
def relator : Fin 5 → List Bool :=
  ![[false, false], [true, true, true],
    (List.replicate 14 [false, true]).flatten,
    (List.replicate 11 [false, true, false, true, false, true, true]).flatten,
    (List.replicate 11 [false, true, false, true, false, true, false, true, true]).flatten]

def quotientStep (s : Bool) (v : V) : V := if s then actY v else actX v

def inputMask (s : Bool) (i : Fin 11) : BitVec 22 :=
  BitVec.ofNat 22 (2 ^ (i.val + if s then 11 else 0))

def inputVector (s : Bool) (v : V) : BitVec 22 := substitute (inputMask s) v

/-- A completely arbitrary central-line lift of the two certified matrices. -/
def liftStep (d : Fin 22 → Bool) (s : Bool) (w : V × Bool) : V × Bool :=
  (quotientStep s w.1, w.2 + evalRow d (inputVector s w.1))

def liftWord (d : Fin 22 → Bool) (w : List Bool) (v : V × Bool) : V × Bool :=
  w.foldl (fun a s => liftStep d s a) v

def wordConstraint : List Bool → V → BitVec 22
  | [], _ => 0
  | s :: w, v => inputVector s v ^^^ wordConstraint w (quotientStep s v)

theorem liftWord_lower (d : Fin 22 → Bool) (w : List Bool) (v : V × Bool) :
    (liftWord d w v).2 = v.2 + evalRow d (wordConstraint w v.1) := by
  induction w generalizing v with
  | nil => simp only [liftWord, List.foldl_nil, wordConstraint, evalRow_zero, add_zero]
  | cons s w ih =>
    change (liftWord d w (liftStep d s v)).2 = _
    rw [ih]
    simp only [liftStep, wordConstraint, evalRow_xor, add_assoc]

/-- Eleven independent equations, selected from the five relators. -/
def constraintMasks : Fin 11 → BitVec 22 :=
  ![3, 12, 96, 768, 928, 14336, 114688, 917504, 4097, 261680, 124958]

def constraintPlaces : Fin 11 → Fin 5 × Fin 11 :=
  ![(0,0), (0,2), (0,5), (0,8), (0,10), (1,0), (1,3), (1,6), (2,1), (3,0), (4,1)]

set_option maxRecDepth 10000 in
theorem constraintMasks_spec : ∀ i : Fin 11,
    wordConstraint (relator (constraintPlaces i).1)
      (BitVec.ofNat 11 (2 ^ (constraintPlaces i).2.val)) = constraintMasks i := by
  decide +kernel

/-- The explicit correction is obtained by solving the generator coboundaries. -/
def correctionMasks : Fin 11 → BitVec 22 :=
  ![2100257, 2100256, 2098209, 2098213, 2114597, 2147365,
    2147333, 2146597, 2408741, 2408485, 3457061]

def correction (d : Fin 22 → Bool) (i : Fin 11) : Bool := evalRow d (correctionMasks i)

def certificateX : Fin 11 → V := ![0, 1, 0, 2, 1379, 0, 4, 24, 0, 8, 0]
def certificateY : Fin 11 → V := ![0, 256, 288, 0, 0, 64, 1803, 0, 1931, 0, 0]

set_option maxRecDepth 10000 in
theorem correction_certificate_x : ∀ i : Fin 11,
    inputMask false i =
      (substitute correctionMasks (BitVec.ofNat 11 (xMasks i)) ^^^ correctionMasks i ^^^
        substitute constraintMasks (certificateX i)) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem correction_certificate_y : ∀ i : Fin 11,
    inputMask true i =
      (substitute correctionMasks (BitVec.ofNat 11 (yMasks i)) ^^^ correctionMasks i ^^^
        substitute constraintMasks (certificateY i)) := by
  decide +kernel

theorem constraints_of_relators (d : Fin 22 → Bool)
    (h : ∀ r : Fin 5, ∀ w : V × Bool, liftWord d (relator r) w = w) :
    ∀ i, evalRow d (constraintMasks i) = 0 := by
  intro i
  have hi := congrArg Prod.snd (h (constraintPlaces i).1
    (BitVec.ofNat 11 (2 ^ (constraintPlaces i).2.val), 0))
  rw [liftWord_lower, constraintMasks_spec, zero_add] at hi
  exact hi

theorem correction_column (d : Fin 22 → Bool)
    (h : ∀ i, evalRow d (constraintMasks i) = 0) (s : Bool) (i : Fin 11) :
    evalRow d (inputMask s i) =
      evalRow (correction d) (BitVec.ofNat 11 ((if s then yMasks else xMasks) i)) +
        correction d i := by
  have hz (v : V) : evalRow d (substitute constraintMasks v) = 0 := by
    rw [evalRow_substitute]
    simp_rw [h]
    simp only [evalRow, mul_zero, Finset.sum_const_zero]
  cases s
  · rw [correction_certificate_x, evalRow_xor, evalRow_xor, hz, add_zero,
      evalRow_substitute]
    rfl
  · rw [correction_certificate_y, evalRow_xor, evalRow_xor, hz, add_zero,
      evalRow_substitute]
    rfl

theorem correction_step (d : Fin 22 → Bool)
    (h : ∀ i, evalRow d (constraintMasks i) = 0) (s : Bool) (v : V) :
    evalRow d (inputVector s v) =
      evalRow (correction d) (quotientStep s v) + evalRow (correction d) v := by
  rw [inputVector, evalRow_substitute]
  simp_rw [correction_column d h]
  simp only [evalRow, mul_add, Finset.sum_add_distrib]
  congr 1
  change evalRow (fun i => evalRow (correction d)
    (BitVec.ofNat 11 ((if s then yMasks else xMasks) i))) v = _
  rw [← evalRow_substitute]
  cases s <;> rfl

/-- The corrected lower coordinate is fixed by both lifted generators. -/
theorem fixed_functional (d : Fin 22 → Bool)
    (h : ∀ r : Fin 5, ∀ w : V × Bool, liftWord d (relator r) w = w)
    (s : Bool) (w : V × Bool) :
    (liftStep d s w).2 + evalRow (correction d) (liftStep d s w).1 =
      w.2 + evalRow (correction d) w.1 := by
  simp only [liftStep, correction_step d (constraints_of_relators d h)]
  ring_nf
  simp only [show (2 : Bool) = 0 from rfl, mul_zero, add_zero]

/-- The functional separates the distinguished central line. -/
def functional (d : Fin 22 → Bool) (w : V × Bool) : Bool :=
  w.2 + evalRow (correction d) w.1

theorem functional_central (d : Fin 22 → Bool) : functional d (0, true) = true := by
  simp only [functional, evalRow_zero, add_zero]

theorem functional_add (d : Fin 22 → Bool) (v w : V × Bool) :
    functional d (v.1 ^^^ w.1, v.2 + w.2) = functional d v + functional d w := by
  simp only [functional, evalRow_xor]
  ac_rfl

/-- Every lift satisfying the actual quotient relators admits an additive
functional, nonzero on the central line and fixed by both generators. -/
theorem exists_fixed_functional (d : Fin 22 → Bool)
    (h : ∀ r : Fin 5, ∀ w : V × Bool, liftWord d (relator r) w = w) :
    ∃ f : V × Bool → Bool, f (0, true) = true ∧
      (∀ v w, f (v.1 ^^^ w.1, v.2 + w.2) = f v + f w) ∧
      ∀ s w, f (liftStep d s w) = f w :=
  ⟨functional d, functional_central d, functional_add d,
    fun s w => fixed_functional d h s w⟩

end Janko4.TwoPrimary.InvariantComplement
