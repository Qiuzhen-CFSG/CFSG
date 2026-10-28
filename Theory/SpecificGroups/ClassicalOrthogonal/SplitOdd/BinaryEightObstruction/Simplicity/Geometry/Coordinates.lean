/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The Siegel conventions are inherited from the attributed ATLAS adaptation in
Simplicity.Basic; this module supplies binary coordinate certificates.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Basic

/-!
# Binary coordinates for the split-eight singular action

The 24 pairs of perpendicular coordinate basis vectors give actual Siegel
roots in `OmegaPlus 4 (ZMod 2)`. Packed binary addition computes their action;
`generator_action` and `decode_step` prove agreement with the natural linear
map, for every input vector. A trace records each intermediate vector so that
checking a root word never repeatedly expands earlier linear maps.

The finite encoding covers every vector, not only the vectors reached by the
roots. These are the coordinate inputs to the rank-three singular geometry
argument of `Geometry.lean`, following the geometric route in ATLAS
`LinearGroups/Orthogonal/SingularPrimitiveD.lean`.
-/

open ClassicalOrthogonal
open ClassicalOrthogonal.BinaryEightObstruction.Simplicity
@[expose] public section
namespace ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry
abbrev Byte := Fin 256
def encode (x : V) : Byte :=
  ⟨(x (.inl 0)).val + 2*(x (.inl 1)).val + 4*(x (.inl 2)).val + 8*(x (.inl 3)).val +
   16*(x (.inr 0)).val + 32*(x (.inr 1)).val + 64*(x (.inr 2)).val + 128*(x (.inr 3)).val, by
    have h0 := ZMod.val_lt (x (.inl 0)); have h1 := ZMod.val_lt (x (.inl 1))
    have h2 := ZMod.val_lt (x (.inl 2)); have h3 := ZMod.val_lt (x (.inl 3))
    have h4 := ZMod.val_lt (x (.inr 0)); have h5 := ZMod.val_lt (x (.inr 1))
    have h6 := ZMod.val_lt (x (.inr 2)); have h7 := ZMod.val_lt (x (.inr 3))
    omega⟩
def opposite : Index 4 → Index 4
  | .inl i => .inr i
  | .inr i => .inl i

def basis (i : Index 4) : V := Pi.single i 1

def pairs : Fin 24 → Index 4 × Index 4 := ![
  ((.inl 0), (.inl 1)),
  ((.inl 0), (.inl 2)),
  ((.inl 0), (.inl 3)),
  ((.inl 0), (.inr 1)),
  ((.inl 0), (.inr 2)),
  ((.inl 0), (.inr 3)),
  ((.inl 1), (.inl 2)),
  ((.inl 1), (.inl 3)),
  ((.inl 1), (.inr 0)),
  ((.inl 1), (.inr 2)),
  ((.inl 1), (.inr 3)),
  ((.inl 2), (.inl 3)),
  ((.inl 2), (.inr 0)),
  ((.inl 2), (.inr 1)),
  ((.inl 2), (.inr 3)),
  ((.inl 3), (.inr 0)),
  ((.inl 3), (.inr 1)),
  ((.inl 3), (.inr 2)),
  ((.inr 0), (.inr 1)),
  ((.inr 0), (.inr 2)),
  ((.inr 0), (.inr 3)),
  ((.inr 1), (.inr 2)),
  ((.inr 1), (.inr 3)),
  ((.inr 2), (.inr 3))]


def position : Index 4 → ℕ
  | .inl i => i.val
  | .inr i => i.val + 4

def bit (n k : ℕ) : K := if n.testBit k then 1 else 0

def decode (n : ℕ) : V := fun i => bit n (position i)

theorem bit_xor (a b k : ℕ) : bit (a ^^^ b) k = bit a k + bit b k := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem decode_xor (a b : ℕ) : decode (a ^^^ b) = decode a + decode b := by
  funext i
  exact bit_xor a b (position i)

theorem position_injective : Function.Injective position := by
  intro i j h
  cases i with
  | inl i => cases j with
    | inl j => congr; exact Fin.ext h
    | inr j => simp only [position] at h; omega
  | inr i => cases j with
    | inl j => simp only [position] at h; omega
    | inr j => congr; apply Fin.ext; simpa only [position, Nat.add_right_cancel_iff] using h

theorem decode_basis (i : Index 4) : decode (2 ^ position i) = basis i := by
  funext j
  simp only [decode, bit, Nat.testBit_two_pow, basis, Pi.single_apply]
  simp [position_injective.eq_iff, eq_comm]

theorem decode_zero : decode 0 = 0 := by
  funext i
  simp [decode, bit]

def stepCode (r : Fin 24) (n : ℕ) : ℕ :=
  (n ^^^ (if n.testBit (position (opposite (pairs r).2)) then 2 ^ position (pairs r).1 else 0)) ^^^
    (if n.testBit (position (opposite (pairs r).1)) then 2 ^ position (pairs r).2 else 0)

def step (r : Fin 24) (x : V) : V :=
  x + x (opposite (pairs r).2) • basis (pairs r).1 +
    x (opposite (pairs r).1) • basis (pairs r).2

theorem decode_step (r : Fin 24) (n : ℕ) : decode (stepCode r n) = step r (decode n) := by
  have h (i j : Index 4) :
      decode (if n.testBit (position i) then 2 ^ position j else 0) =
        decode n i • basis j := by
    cases hb : n.testBit (position i) <;>
      simp only [Bool.false_eq_true, if_false, if_true, decode_basis, decode_zero,
        decode, bit, hb, zero_smul, one_smul]
  rw [stepCode, decode_xor, decode_xor, h, h]
  rfl

theorem decode_encode : ∀ v : V, decode (encode v).val = v := by decide +kernel

theorem basis_singular (i : Index 4) : Q (basis i) = 0 := by
  cases i with
  | inl i => exact formD_e i
  | inr i => exact formD_f i

theorem polar_basis (x : V) (i : Index 4) : Q.polarBilin x (basis i) = x (opposite i) := by
  cases i with
  | inl i => exact polarD_e x i
  | inr i => exact polarD_f x i

theorem pair_perpendicular : ∀ r : Fin 24, basis (pairs r).1 (opposite (pairs r).2) = 0 := by
  decide +kernel

noncomputable def generator (r : Fin 24) : E :=
  root (basis (pairs r).1) (basis (pairs r).2) (basis_singular _) (by
    rw [polar_basis]; exact pair_perpendicular r)

theorem generator_action (r : Fin 24) (x : V) : linear (generator r) x = step r x := by
  rw [generator, linear_root]
  simp only [Quadratic.siegel, polar_basis, basis_singular, zero_mul, zero_smul, sub_zero]
  ext i
  simp [step, sub_eq_add_neg]

def fastQ (x : V) : K :=
  x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) +
  x (.inl 2) * x (.inr 2) + x (.inl 3) * x (.inr 3)

theorem fastQ_eq (x : V) : fastQ x = Q x := by
  simp [fastQ, formD_apply, Fin.sum_univ_succ, add_assoc]

theorem decode_one : decode 1 = e 0 := by decide +kernel
theorem decode_two : decode 2 = e 1 := by decide +kernel
theorem decode_sixteen : decode 16 = f 0 := by decide +kernel


abbrev Trace := List (Fin 24 × ℕ)

def checkPath : ℕ → ℕ → Trace → Bool
  | start, target, [] => decide (start = target)
  | start, target, (r, next) :: tail =>
    decide (stepCode r start = next) && checkPath next target tail

def checkFixed (trace : Trace) : Bool := trace.all (fun s => decide (stepCode s.1 1 = 1))

noncomputable def pathElement : Trace → E
  | [] => 1
  | (r, _) :: tail => pathElement tail * generator r

theorem path_action (start target : ℕ) (trace : Trace) (h : checkPath start target trace = true) :
    linear (pathElement trace) (decode start) = decode target := by
  induction trace generalizing start with
  | nil =>
    have he : start = target := of_decide_eq_true h
    subst target
    rfl
  | cons s tail ih =>
    rcases s with ⟨r, next⟩
    simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at h
    change linear (pathElement tail) (linear (generator r) (decode start)) = _
    rw [generator_action, ← decode_step, h.1]
    exact ih next h.2

theorem path_fixes (trace : Trace) (h : checkFixed trace = true) :
    linear (pathElement trace) (decode 1) = decode 1 := by
  induction trace with
  | nil => rfl
  | cons s tail ih =>
    rcases s with ⟨r, next⟩
    simp only [checkFixed, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    change linear (pathElement tail) (linear (generator r) (decode 1)) = _
    rw [generator_action, ← decode_step, h.1]
    exact ih h.2


end ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry
