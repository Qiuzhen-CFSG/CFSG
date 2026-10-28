module

public import Theory.SpecificGroups.C4SquareSignSwap
public import Mathlib.Data.Fin.VecNotation

/-!
# Concrete candidates for centric subgroups of the sign-and-swap group

The coordinate code of `(a,b,s,t)` is `a + 4*b + 16*s + 32*t`.
The masks below specify actual subgroups of the explicit order-64 model.
Their closure laws are checked by the Lean kernel.
The numbering is fixed by the displayed generator tuples, not by an external
small-group catalogue. No completeness or automorphism classification is
asserted in this data module.

These finite subgroup calculations support the intrinsic centric
classification for the model of Stellmacher (8.6)(a); see
`refs/latex/stellmacher-n-group.tex` and `C4SquareSignSwap`.
-/

namespace C4SquareSignSwap

/-- Encode the four coordinates as an integer in `[0,64)`. -/
@[expose] public def coordinateCode (g : Model) : ℕ :=
  g.left.1.toAdd.val + 4 * g.left.2.toAdd.val +
    16 * g.right.1.toAdd.val + 32 * g.right.2.toAdd.val

/-- Decode a coordinate code, reducing it modulo 64. -/
@[expose] public def coordinateElement (n : ℕ) : Model :=
  ⟨(Multiplicative.ofAdd (n : ZMod 4), Multiplicative.ofAdd ((n / 4 : ℕ) : ZMod 4)),
    (Multiplicative.ofAdd ((n / 16 : ℕ) : ZMod 2),
      Multiplicative.ofAdd ((n / 32 : ℕ) : ZMod 2))⟩

public theorem coordinateElement_coordinateCode :
    ∀ g : Model, coordinateElement (coordinateCode g) = g := by decide +kernel

/-- The carrier masks, with their generating codes recorded beside each entry. -/
@[expose] public def centricCandidateMask : Fin 32 → ℕ :=
  ![5193213320311612545 /- 0: (49,) -/,
    18446462598732906495 /- 1: (1, 48) -/,
    6510516211317515685 /- 2: (2, 49) -/,
    2630383657361089665 /- 3: (7, 48) -/,
    6510615556690126245 /- 4: (16, 33) -/,
    73184610703442945 /- 5: (16, 34) -/,
    5193253457990132865 /- 6: (17, 32) -/,
    9520917759391859745 /- 7: (17, 33) -/,
    1317444883833824385 /- 8: (17, 34) -/,
    2415127971431089185 /- 9: (17, 35) -/,
    2341872925073736705 /- 10: (21, 34) -/,
    4294967295 /- 11: (1, 4, 16) -/,
    252645135 /- 12: (1, 8, 16) -/,
    4042264335 /- 13: (1, 8, 20) -/,
    18446744073709551615 /- 14: (1, 16, 32) -/,
    2779096485 /- 15: (2, 5, 16) -/,
    1515890085 /- 16: (2, 5, 17) -/,
    11935946387415410085 /- 17: (2, 5, 48) -/,
    84215045 /- 18: (2, 8, 16) -/,
    168428805 /- 19: (2, 8, 17) -/,
    2694841605 /- 20: (2, 8, 21) -/,
    361700864190383365 /- 21: (2, 16, 32) -/,
    6510698340921550245 /- 22: (2, 17, 32) -/,
    11936045731524814245 /- 23: (2, 17, 33) -/,
    11574256564069991685 /- 24: (2, 21, 32) -/,
    9521036366723515425 /- 25: (5, 16, 32) -/,
    2415092153213617185 /- 26: (5, 16, 34) -/,
    2630423794442904705 /- 27: (7, 16, 32) -/,
    9305704722285536385 /- 28: (7, 16, 34) -/,
    288516253537076225 /- 29: (10, 16, 32) -/,
    9232383640600577025 /- 30: (10, 21, 32) -/,
    11936128518282651045 /- 31: (2, 5, 16, 32) -/]

@[expose] public def centricCandidateMember (i : Fin 32) (g : Model) : Prop :=
  (centricCandidateMask i).testBit (coordinateCode g) = true

public instance (i : Fin 32) (g : Model) : Decidable (centricCandidateMember i g) :=
  inferInstanceAs (Decidable (_ = _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem centricCandidate_closed : ∀ i : Fin 32,
    centricCandidateMember i 1 ∧
    (∀ a b : Model, centricCandidateMember i a → centricCandidateMember i b →
      centricCandidateMember i (a * b)) ∧
    (∀ a : Model, centricCandidateMember i a → centricCandidateMember i a⁻¹) := by
  decide +kernel

/-- A concrete subgroup specified by its coordinate mask. -/
@[expose] public def centricCandidate (i : Fin 32) : Subgroup Model where
  carrier := centricCandidateMember i
  one_mem' := by exact (centricCandidate_closed i).1
  mul_mem' := by exact (centricCandidate_closed i).2.1 _ _
  inv_mem' := by exact (centricCandidate_closed i).2.2 _

public instance (i : Fin 32) : DecidablePred (· ∈ centricCandidate i) :=
  fun g => inferInstanceAs (Decidable (centricCandidateMember i g))

end C4SquareSignSwap
