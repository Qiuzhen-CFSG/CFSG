module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Certificate
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.ReferenceMatrix

/-!
# Reflected binary matrix certificates

Boolean parity computes binary dot products. The proved reflection lemmas
turn the finite checks into matrix fixed-vector and left-inverse equations.
A residue modulo sixteen determines the integral quotient by eight modulo two,
for both a signed coordinate action and its negative. The alternative array
storage is checked against the existing integral lattice basis.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
These checks support the literal Leech quotient, using its established basis.
-/
open Atlas.Codes
open scoped BigOperators Matrix
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
namespace FrameCheck

def bitVal (b : Bool) : Bit := if b then 1 else 0

theorem bitVal_and (a b : Bool) : bitVal (a && b) = bitVal a * bitVal b := by
  cases a <;> cases b <;> decide

theorem bitVal_xor (a b : Bool) : bitVal (a ^^ b) = bitVal a + bitVal b := by
  cases a <;> cases b <;> decide

def all8 (f : Fin 8 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7

theorem all8_iff (f : Fin 8 → Bool) : all8 f = true ↔ ∀ i, f i = true := by
  simp only [all8, Bool.and_eq_true]
  constructor
  · intro h i
    fin_cases i <;> tauto
  · intro h
    tauto

def all24 (f : Fin 24 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7 && f 8 && f 9 && f 10 && f 11 && f 12 && f 13 && f 14 && f 15 && f 16 && f 17 && f 18 && f 19 && f 20 && f 21 && f 22 && f 23

theorem all24_iff (f : Fin 24 → Bool) : all24 f = true ↔ ∀ i, f i = true := by
  simp only [all24, Bool.and_eq_true]
  constructor
  · intro h i
    fin_cases i <;> tauto
  · intro h
    tauto

def parity24 (f : Fin 24 → Bool) : Bool :=
  f 0 ^^ f 1 ^^ f 2 ^^ f 3 ^^ f 4 ^^ f 5 ^^ f 6 ^^ f 7 ^^ f 8 ^^ f 9 ^^ f 10 ^^ f 11 ^^ f 12 ^^ f 13 ^^ f 14 ^^ f 15 ^^ f 16 ^^ f 17 ^^ f 18 ^^ f 19 ^^ f 20 ^^ f 21 ^^ f 22 ^^ f 23

theorem bitVal_parity24 (f : Fin 24 → Bool) :
    bitVal (parity24 f) = ∑ i, bitVal (f i) := by
  simp only [parity24, bitVal_xor, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change bitVal (f 0) + bitVal (f 1) + bitVal (f 2) + bitVal (f 3) + bitVal (f 4) + bitVal (f 5) + bitVal (f 6) + bitVal (f 7) + bitVal (f 8) + bitVal (f 9) + bitVal (f 10) + bitVal (f 11) + bitVal (f 12) + bitVal (f 13) + bitVal (f 14) + bitVal (f 15) + bitVal (f 16) + bitVal (f 17) + bitVal (f 18) + bitVal (f 19) + bitVal (f 20) + bitVal (f 21) + bitVal (f 22) + bitVal (f 23) = bitVal (f 0) + (bitVal (f 1) + (bitVal (f 2) + (bitVal (f 3) + (bitVal (f 4) + (bitVal (f 5) + (bitVal (f 6) + (bitVal (f 7) + (bitVal (f 8) + (bitVal (f 9) + (bitVal (f 10) + (bitVal (f 11) + (bitVal (f 12) + (bitVal (f 13) + (bitVal (f 14) + (bitVal (f 15) + (bitVal (f 16) + (bitVal (f 17) + (bitVal (f 18) + (bitVal (f 19) + (bitVal (f 20) + (bitVal (f 21) + (bitVal (f 22) + (bitVal (f 23))))))))))))))))))))))))
  simp only [add_assoc]

def dot24 (a b : ℕ) : Bool := parity24 (fun k => a.testBit k.val && b.testBit k.val)

theorem dot24_eq (a b : ℕ) :
    (∑ k : Fin 24, maskBit a k * maskBit b k) = bitVal (dot24 a b) := by
  unfold dot24
  rw [bitVal_parity24]
  simp only [bitVal_and]
  rfl

def rowMatrix (rows : Vector ℕ 24) : Matrix (Fin 24) (Fin 24) Bit :=
  fun i => maskBit (rows.get i)

def colMatrix (cols : Vector ℕ 8) : Matrix (Fin 24) (Fin 8) Bit :=
  fun i j => maskBit (cols.get j) i

def fixedCheck (rows : Vector ℕ 24) (cols : Vector ℕ 8) : Bool :=
  all24 fun i => all8 fun j => dot24 (rows.get i) (cols.get j) == (cols.get j).testBit i.val

theorem fixed_of_check (rows : Vector ℕ 24) (cols : Vector ℕ 8)
    (h : fixedCheck rows cols = true) : rowMatrix rows * colMatrix cols = colMatrix cols := by
  apply Matrix.ext
  intro i j
  have h' := (all8_iff _).mp ((all24_iff _).mp h i) j
  have hb : dot24 (rows.get i) (cols.get j) = (cols.get j).testBit i.val := by
    simpa only [beq_iff_eq] using h'
  change (∑ k : Fin 24, maskBit (rows.get i) k * maskBit (cols.get j) k) = _
  rw [dot24_eq, hb]
  rfl

def coordinateRetract (p : Vector (Fin 24) 8) : Matrix (Fin 8) (Fin 24) Bit :=
  fun i j => if p.get i = j then 1 else 0

def independentCheck (p : Vector (Fin 24) 8) (cols : Vector ℕ 8) : Bool :=
  all8 fun i => all8 fun j => (cols.get j).testBit (p.get i).val == decide (i = j)

theorem independent_of_check (p : Vector (Fin 24) 8) (cols : Vector ℕ 8)
    (h : independentCheck p cols = true) : coordinateRetract p * colMatrix cols = 1 := by
  apply Matrix.ext
  intro i j
  have h' := (all8_iff _).mp ((all8_iff _).mp h i) j
  have hb : (cols.get j).testBit (p.get i).val = decide (i = j) := by
    simpa only [beq_iff_eq] using h'
  simp only [Matrix.mul_apply, coordinateRetract, colMatrix, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, maskBit, hb]
  simp [Matrix.one_apply]

def basisArray : Vector (Vector ℤ 24) 24 := ⟨#[⟨#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,2,2,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,2,2,0,0,0,0,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,0,0,2,2,0,0,2,2,0,0,2,4,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,2,0,2,0,2,0,0,2,2,0,2,0,4,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,2,0,2,0,2,2,0,2,0,2,0,2,0,0,4,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,2,0,2,0,2,0,2,2,0,0,0,0,0,0,2,4,0,0,0,0,0,0], rfl⟩,
⟨#[1,0,0,2,2,2,0,0,2,0,2,0,0,0,0,0,2,0,4,0,0,0,0,0], rfl⟩,
⟨#[1,2,0,0,0,2,2,0,0,2,2,0,0,0,0,0,2,0,0,4,0,0,0,0], rfl⟩,
⟨#[1,2,2,2,2,0,0,0,2,0,0,0,2,0,0,0,2,0,0,0,4,0,0,0], rfl⟩,
⟨#[1,0,0,2,2,2,2,0,0,2,0,0,2,0,0,0,2,0,0,0,0,4,0,0], rfl⟩,
⟨#[1,0,2,0,0,2,0,0,2,2,2,0,2,0,0,0,2,0,0,0,0,0,4,0], rfl⟩,
⟨#[5,0,2,2,0,0,2,4,0,0,2,4,2,4,4,4,2,4,4,4,4,4,4,8], rfl⟩], rfl⟩


set_option Elab.async false in
theorem basisArray_check : all24 (fun i => all24 (fun j =>
    decide (StandardCoordinates.basisMatrix i j = (basisArray.get i).get j))) = true := by
  decide +kernel

theorem basisArray_eq : StandardCoordinates.basisMatrix = (fun i j => (basisArray.get i).get j) := by
  funext i j
  exact of_decide_eq_true ((all24_iff _).mp ((all24_iff _).mp basisArray_check i) j)

theorem mod16_to_bit (z : ℤ) (b : Bool) (h : z % 16 = if b then 8 else 0) :
    ((z / 8 : ℤ) : Bit) = bitVal b ∧ (((-z) / 8 : ℤ) : Bit) = bitVal b := by
  cases b <;> constructor
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true] at h
    unfold bitVal
    norm_num only [Bool.false_eq_true, if_false, if_true]
  · change ((z / 8 : ℤ) : ZMod 2) = ((0 : ℤ) : ZMod 2)
    rw [ZMod.intCast_eq_intCast_iff']
    omega
  · change (((-z) / 8 : ℤ) : ZMod 2) = ((0 : ℤ) : ZMod 2)
    rw [ZMod.intCast_eq_intCast_iff']
    omega
  · change ((z / 8 : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2)
    rw [ZMod.intCast_eq_intCast_iff']
    omega
  · change (((-z) / 8 : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2)
    rw [ZMod.intCast_eq_intCast_iff']
    omega

end FrameCheck
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
