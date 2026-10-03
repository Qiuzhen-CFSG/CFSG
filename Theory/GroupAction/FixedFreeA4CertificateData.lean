module
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

/-!
# Binary data for the fixed-free A4 plane obstruction

Four binary columns encode endomorphisms of the elementary group of order
sixteen. The standard reflection and cubic have their literal column values.
The fifty-three word patterns below express the reflection as a product of
two commutators of its conjugates whenever the selected pattern succeeds.
Separate kernel-checked row modules certify that a pattern succeeds for every
invertible matrix moving the reflection plane. The main group-action module
interprets these literal computations in the supplied automorphism subgroup.

The Boolean checks are related to their mathematical propositions here; no
finite classification or trust axiom is assumed. The data supports the
source-neutral repair of Stellmacher (8.6)(b3), printed p.44.
-/

@[expose] public section
namespace FixedFreeA4BinaryData
abbrev B := Fin 16
abbrev Code := B × B × B × B
def xor (a b : B) : B := (BitVec.ofFin (w := 4) a ^^^ BitVec.ofFin (w := 4) b).toFin
def applyCode (c : Code) (v : B) : B :=
  xor (xor (xor (if v.val.testBit 0 then c.1 else 0)
    (if v.val.testBit 1 then c.2.1 else 0))
    (if v.val.testBit 2 then c.2.2.1 else 0))
    (if v.val.testBit 3 then c.2.2.2 else 0)
def mulCode (a b : Code) : Code :=
  (applyCode a b.1,applyCode a b.2.1,applyCode a b.2.2.1,applyCode a b.2.2.2)
def identity : Code := (1,2,4,8)
def reflection : Code := (1,2,5,10)
def cubic : Code := (2,3,12,4)
def cubicInv : Code := (3,1,8,12)
def preimage (c : Code) (b : B) : B :=
  ((List.finRange 16).find? (fun v => applyCode c v = b)).getD 0
def inverseCode (c : Code) : Code :=
  (preimage c 1,preimage c 2,preimage c 4,preimage c 8)
def good (c : Code) : Prop := ∀ v : B, applyCode c v = 0 → v = 0
instance (c : Code) : Decidable (good c) := inferInstanceAs
  (Decidable (∀ v : B, applyCode c v = 0 → v = 0))
def moves (c : Code) : Prop := 4 ≤ c.1.val ∨ 4 ≤ c.2.1.val
instance (c : Code) : Decidable (moves c) := inferInstanceAs
  (Decidable (4 ≤ c.1.val ∨ 4 ≤ c.2.1.val))
def letter (g : Code) (k : Fin 5) : Code :=
  ![reflection,cubic,cubicInv,g,inverseCode g] k
def inverseLetter (g : Code) (k : Fin 5) : Code :=
  ![reflection,cubicInv,cubic,inverseCode g,g] k
def conjugateWord (g : Code) : List (Fin 5) → Code
  | [] => reflection
  | k::w => mulCode (mulCode (letter g k) (conjugateWord g w)) (inverseLetter g k)
def commutatorInvolutions (a b : Code) : Code :=
  mulCode (mulCode (mulCode a b) a) b
def certificates : Fin 53 → (List (Fin 5)) × (List (Fin 5)) × (List (Fin 5)) × (List (Fin 5)) := ![
  ([2], [3], [1], [1, 3]),
  ([], [2, 3, 3, 3], [], [1, 3, 3, 3]),
  ([], [1, 4], [], [4]),
  ([], [2, 4], [], [4]),
  ([], [3, 2], [], [4, 1]),
  ([], [4, 2], [], [3, 1]),
  ([2], [3], [1], [0, 1, 3]),
  ([], [1, 3, 1], [], [3, 1]),
  ([], [2, 3, 2], [], [3, 2]),
  ([], [2, 3, 0, 3, 2], [], [3, 0, 3, 2]),
  ([], [1, 3, 0, 3, 1], [], [3, 0, 3, 1]),
  ([], [4, 0, 4, 2], [], [3, 0, 3, 1]),
  ([], [4, 4, 0, 4], [], [3, 3, 0, 3]),
  ([], [3, 0, 3, 2], [], [4, 0, 4, 1]),
  ([], [2, 3, 3], [], [1, 3, 3]),
  ([2], [3], [1], [3, 1]),
  ([], [2, 3, 3], [], [3, 3]),
  ([], [1, 4, 4], [], [4, 4]),
  ([2], [3], [1], [3, 2]),
  ([], [2, 4, 4], [], [4, 4]),
  ([], [1, 3, 0, 3], [], [3, 0, 3]),
  ([2], [3], [1], [2, 0, 3, 1]),
  ([2], [3], [1], [2, 3, 1]),
  ([2], [3], [1], [0, 3, 1]),
  ([], [4, 0, 3, 3], [], [3, 3, 3, 1]),
  ([], [4, 0, 3, 3], [], [3, 3, 3, 2]),
  ([], [2, 3, 3, 2], [], [3, 3, 2]),
  ([], [1, 3, 3, 1], [], [3, 3, 1]),
  ([], [1, 4, 0, 4], [], [4, 0, 4]),
  ([], [2, 4, 0, 4], [], [4, 0, 4]),
  ([], [2, 3, 0, 3], [], [3, 0, 3]),
  ([], [3, 3, 2], [], [4, 4, 1]),
  ([], [1, 3, 3], [], [3, 2, 3]),
  ([], [4, 0, 3, 1, 0, 3], [], [3, 0, 3, 1, 0, 3]),
  ([], [4, 0, 3, 1, 3], [], [3, 0, 3, 1, 3]),
  ([], [3, 0, 4, 2, 0, 3], [], [4, 0, 4, 0, 3]),
  ([], [3, 0, 4, 1, 0, 3], [], [4, 0, 4, 0, 3]),
  ([], [1, 3, 2, 3, 0, 3], [], [3, 2, 3, 0, 3]),
  ([2], [3], [1], [2, 0, 4, 1]),
  ([], [3, 3, 1, 4], [], [3, 3, 3, 1]),
  ([], [3, 3, 2, 4], [], [3, 3, 3, 2]),
  ([2], [3], [1], [2, 4, 1]),
  ([2], [3], [1], [3, 3]),
  ([2], [3], [1], [4]),
  ([], [3, 1, 3, 1, 3], [], [3, 1, 3, 0, 3]),
  ([], [3, 2, 3, 2, 3], [], [3, 2, 3, 0, 3]),
  ([], [4, 4, 1, 3], [], [3, 3, 3, 1]),
  ([], [4, 4, 2, 3], [], [3, 3, 3, 2]),
  ([], [3, 3, 2, 4], [], [3, 3, 3, 1]),
  ([], [4, 4, 1, 3], [], [3, 3, 3, 2]),
  ([], [2, 3, 1, 3, 0, 3], [], [3, 1, 3, 0, 3]),
  ([], [4, 4, 2, 3], [], [3, 3, 3, 1]),
  ([], [3, 3, 1, 4], [], [3, 3, 3, 2])]
def perfect (g : Code) (k : Fin 53) : Prop :=
  let w := certificates k
  mulCode (commutatorInvolutions (conjugateWord g w.1) (conjugateWord g w.2.1))
    (commutatorInvolutions (conjugateWord g w.2.2.1) (conjugateWord g w.2.2.2)) = reflection
instance (g : Code) (k : Fin 53) : Decidable (perfect g k) :=
  inferInstanceAs (Decidable (_ = _))
def goodBool (g : Code) : Bool :=
  (List.finRange 16).all (fun b => applyCode g b != 0 || b == 0)
def movesBool (g : Code) : Bool := decide (4 ≤ g.1.val) || decide (4 ≤ g.2.1.val)
def perfectBool (g : Code) (k : Fin 53) : Bool :=
  let w := certificates k
  mulCode (commutatorInvolutions (conjugateWord g w.1) (conjugateWord g w.2.1))
    (commutatorInvolutions (conjugateWord g w.2.2.1) (conjugateWord g w.2.2.2)) == reflection
def checks (g : Code) (k : Fin 53) : Bool :=
  !goodBool g || !movesBool g || perfectBool g k

theorem goodBool_spec (g : Code) : goodBool g = true ↔ good g := by
  simp only [goodBool,List.all_eq_true,List.mem_finRange,forall_true_left,
    Bool.or_eq_true,bne_iff_ne,beq_iff_eq,good]
  constructor
  · intro h b hb
    exact (h b).resolve_left (not_not_intro hb)
  · intro h b
    by_cases hb : applyCode g b=0
    · exact Or.inr (h b hb)
    · exact Or.inl hb

theorem movesBool_spec (g : Code) : movesBool g = true ↔ moves g := by
  simp only [movesBool,Bool.or_eq_true,decide_eq_true_eq,moves]

theorem perfectBool_spec (g : Code) (k : Fin 53) : perfectBool g k = true ↔ perfect g k := by
  simp only [perfectBool,beq_iff_eq,perfect]

/-- A successful Boolean check supplies the selected commutator identity. -/
theorem perfect_of_check (g : Code) (k : Fin 53) (hg : good g) (hm : moves g)
    (hcheck : checks g k = true) : perfect g k := by
  apply (perfectBool_spec g k).mp
  have hgb := (goodBool_spec g).mpr hg
  have hmb := (movesBool_spec g).mpr hm
  simpa only [checks,hgb,hmb,Bool.not_true,Bool.false_or] using hcheck
end FixedFreeA4BinaryData
