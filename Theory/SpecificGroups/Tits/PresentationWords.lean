module

public import Theory.SpecificGroups.Tits.Presentation
import Mathlib.Tactic.Group

/-!
# Signed words for Parrott's relators

This is the literal word interface for coset-enumeration certificates for
Parrott's presentation (1972, §5, p. 683). A `true` sign denotes a generator;
a `false` sign denotes its inverse. The words use the generator and relator
order of `Presentation.lean`.

The equality with every existing free-group relator is checked in Lean by
group normalization. Thus a certificate using these words concerns the actual
presented group; the word table itself makes no assertion of coset coverage.
-/

namespace Tits

/-- The signed words used by the Parrott coset-enumeration certificate. -/
@[expose] public def parrottRelatorWord :
    ParrottRelatorIndex → List (ParrottGenerator × Bool)
  | .i_r1 =>
      [(.r1, true), (.r1, true)]
  | .i_r8 =>
      [(.r8, true), (.r8, true)]
  | .i_s1 =>
      [(.s1, true), (.s1, true)]
  | .i_s2 =>
      [(.s2, true), (.s2, true)]
  | .i_s4 =>
      [(.s4, true), (.s4, true)]
  | .i_s6 =>
      [(.s6, true), (.s6, true)]
  | .i_s8 =>
      [(.s8, true), (.s8, true)]
  | .i_s3 =>
      [(.s3, true), (.s3, true), (.s3, true), (.s3, true)]
  | .i_s5 =>
      [(.s5, true), (.s5, true), (.s5, true), (.s5, true)]
  | .i_s7 =>
      [(.s7, true), (.s7, true), (.s7, true), (.s7, true)]
  | .ii_s1_s2 =>
      [(.s1, false), (.s2, false), (.s1, true), (.s2, true)]
  | .ii_s1_s3 =>
      [(.s1, false), (.s3, false), (.s1, true), (.s3, true)]
  | .ii_s1_s5 =>
      [(.s1, false), (.s5, false), (.s1, true), (.s5, true)]
  | .iii_s1_s6 =>
      [(.s1, false), (.s6, false), (.s1, true), (.s6, true), (.s3, false), (.s3, false),
       (.s2, false), (.s1, false)]
  | .iii_s1_s7 =>
      [(.s1, false), (.s7, false), (.s1, true), (.s7, true), (.s5, false), (.s5, false),
       (.s1, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s2, false)]
  | .iii_s1_s8 =>
      [(.s1, false), (.s8, false), (.s1, true), (.s8, true), (.s1, false), (.s3, false),
       (.s3, false), (.s2, false), (.s1, false), (.s7, false), (.s7, false)]
  | .iv_s2_s4 =>
      [(.s2, false), (.s4, false), (.s2, true), (.s4, true)]
  | .iv_s2_s6 =>
      [(.s2, false), (.s6, false), (.s2, true), (.s6, true)]
  | .iv_s2_s8 =>
      [(.s2, false), (.s8, false), (.s2, true), (.s8, true), (.s6, false), (.s4, false)]
  | .iv_s7_s2 =>
      [(.s7, false), (.s2, false), (.s7, true), (.s2, true), (.s5, false), (.s5, false),
       (.s1, false), (.s4, false)]
  | .v_s7_s4 =>
      [(.s7, false), (.s4, false), (.s7, true), (.s4, true), (.s5, false), (.s5, false),
       (.s1, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false)]
  | .v_s3_s5 =>
      [(.s3, false), (.s5, false), (.s3, true), (.s5, true), (.s4, false), (.s3, false),
       (.s3, false), (.s2, false), (.s1, false), (.s2, false)]
  | .v_s5_s4 =>
      [(.s5, false), (.s4, false), (.s5, true), (.s4, true), (.s3, false), (.s3, false),
       (.s2, false), (.s1, false)]
  | .vi_r1_r8 =>
      [(.r1, true), (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.r8, true), (.r1, true),
       (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.r8, true),
       (.r1, true), (.r8, true)]
  | .vi_s1_r1 =>
      [(.s1, true), (.r1, true), (.s1, true), (.r1, true), (.s1, true), (.r1, true), (.s1, true),
       (.r1, true), (.s1, true), (.r1, true)]
  | .vi_r8_s8 =>
      [(.r8, true), (.s8, true), (.r8, true), (.s8, true), (.r8, true), (.s8, true)]
  | .vii_s2 =>
      [(.r1, true), (.s2, true), (.r1, true), (.s8, false)]
  | .vii_s4 =>
      [(.r1, true), (.s4, true), (.r1, true), (.s6, false)]
  | .vii_s5 =>
      [(.r1, true), (.s5, true), (.r1, true), (.s5, false), (.r1, false), (.s1, false),
       (.r1, false), (.s1, false)]
  | .vii_s3 =>
      [(.r1, true), (.s3, true), (.r1, true), (.s7, false), (.s5, false), (.s3, false),
       (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.r1, false), (.s1, false),
       (.r1, false), (.s1, false)]
  | .vii_r3 =>
      [(.r1, true), (.s1, true), (.s2, true), (.s3, true), (.s3, true), (.r1, true),
       (.s7, false), (.s5, false), (.s3, false), (.s3, false), (.s3, false), (.s2, false),
       (.s1, false), (.s7, false)]
  | .viii_s2 =>
      [(.r8, true), (.s2, true), (.r8, true), (.s6, false)]
  | .viii_s4 =>
      [(.r8, true), (.s4, true), (.r8, true), (.s4, false)]
  | .viii_s1 =>
      [(.r8, true), (.s1, true), (.r8, true), (.s7, false), (.s5, false), (.s3, false),
       (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s7, false)]
  | .viii_s7 =>
      [(.r8, true), (.s7, true), (.r8, true), (.s7, true)]
  | .viii_s3 =>
      [(.r8, true), (.s3, true), (.r8, true), (.s5, false), (.s7, false)]
  | .viii_r3 =>
      [(.r8, true), (.s1, true), (.s2, true), (.s3, true), (.s3, true), (.r8, true),
       (.s5, false), (.s5, false), (.s1, false)]

/-- Every certificate word is exactly its defining relator in the free group. -/
public theorem parrottRelatorWord_eq (r : ParrottRelatorIndex) :
    FreeGroup.mk (parrottRelatorWord r) = parrottRelator r := by
  have cons (a : ParrottGenerator) (b : Bool) (w : List (ParrottGenerator × Bool)) :
      FreeGroup.mk ((a, b) :: w) =
        (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk w := by
    cases b <;> rfl
  have nil : FreeGroup.mk ([] : List (ParrottGenerator × Bool)) = 1 := rfl
  cases r <;>
    simp only [parrottRelatorWord, parrottRelator, parrottCommutator,
      parrottR3, parrottR5, parrottR7, cons, nil, Bool.false_eq_true,
      ↓reduceIte, pow_succ, pow_zero] <;> group

/-- Evaluating each certificate word at the canonical generators gives one. -/
public theorem parrottRelatorWord_eval (r : ParrottRelatorIndex) :
    FreeGroup.lift parrottGenerator (FreeGroup.mk (parrottRelatorWord r)) = 1 := by
  rw [parrottRelatorWord_eq]
  exact parrott_generators_satisfy_relations r

end Tits
