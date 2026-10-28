module

public import Theory.SpecificGroups.Tits.R1WordCertificate.defPairTable

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

@[expose] public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

/-- Acyclic representatives, extended harmlessly beyond the finite input. -/
def definitions : Definitions ParrottR1Generator where
  parent n := min (defPair n).1 (n - 1)
  letter n := (defPair n).2
  parent_lt n := by
    have := Nat.min_le_right (defPair (n + 1)).1 (n + 1 - 1)
    omega

def relatorFin : Fin 28 → Word ParrottR1Generator := fun i => match i.1 with
  | 0 => [(.r1, true), (.r1, true)]
  | 1 => [(.s1, true), (.s1, true)]
  | 2 => [(.s2, true), (.s2, true)]
  | 3 => [(.s4, true), (.s4, true)]
  | 4 => [(.s6, true), (.s6, true)]
  | 5 => [(.s8, true), (.s8, true)]
  | 6 => [(.s3, true), (.s3, true), (.s3, true), (.s3, true)]
  | 7 => [(.s5, true), (.s5, true), (.s5, true), (.s5, true)]
  | 8 => [(.s7, true), (.s7, true), (.s7, true), (.s7, true)]
  | 9 => [(.s1, false), (.s2, false), (.s1, true), (.s2, true)]
  | 10 => [(.s1, false), (.s3, false), (.s1, true), (.s3, true)]
  | 11 => [(.s1, false), (.s5, false), (.s1, true), (.s5, true)]
  | 12 => [(.s1, false), (.s6, false), (.s1, true), (.s6, true), (.s3, false), (.s3, false), (.s2, false), (.s1, false)]
  | 13 => [(.s1, false), (.s7, false), (.s1, true), (.s7, true), (.s5, false), (.s5, false), (.s1, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s2, false)]
  | 14 => [(.s1, false), (.s8, false), (.s1, true), (.s8, true), (.s1, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s7, false), (.s7, false)]
  | 15 => [(.s2, false), (.s4, false), (.s2, true), (.s4, true)]
  | 16 => [(.s2, false), (.s6, false), (.s2, true), (.s6, true)]
  | 17 => [(.s2, false), (.s8, false), (.s2, true), (.s8, true), (.s6, false), (.s4, false)]
  | 18 => [(.s7, false), (.s2, false), (.s7, true), (.s2, true), (.s5, false), (.s5, false), (.s1, false), (.s4, false)]
  | 19 => [(.s7, false), (.s4, false), (.s7, true), (.s4, true), (.s5, false), (.s5, false), (.s1, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false)]
  | 20 => [(.s3, false), (.s5, false), (.s3, true), (.s5, true), (.s4, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s2, false)]
  | 21 => [(.s5, false), (.s4, false), (.s5, true), (.s4, true), (.s3, false), (.s3, false), (.s2, false), (.s1, false)]
  | 22 => [(.s1, true), (.r1, true), (.s1, true), (.r1, true), (.s1, true), (.r1, true), (.s1, true), (.r1, true), (.s1, true), (.r1, true)]
  | 23 => [(.r1, true), (.s2, true), (.r1, true), (.s8, false)]
  | 24 => [(.r1, true), (.s4, true), (.r1, true), (.s6, false)]
  | 25 => [(.r1, true), (.s5, true), (.r1, true), (.s5, false), (.r1, false), (.s1, false), (.r1, false), (.s1, false)]
  | 26 => [(.r1, true), (.s3, true), (.r1, true), (.s7, false), (.s5, false), (.s3, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.r1, false), (.s1, false), (.r1, false), (.s1, false)]
  | 27 => [(.r1, true), (.s1, true), (.s2, true), (.s3, true), (.s3, true), (.r1, true), (.s7, false), (.s5, false), (.s3, false), (.s3, false), (.s3, false), (.s2, false), (.s1, false), (.s7, false)]
  | _ => []

def relatorWords (r : Nat) : Word ParrottR1Generator :=
  if h : r < 28 then relatorFin ⟨r, h⟩ else []

def context : Context ParrottR1Generator :=
  ⟨definitions.parent, definitions.letter, relatorWords,
    fun a => decide (a = (.r1, true) ∨ a = (.s1, true))⟩

end Tits.R1WordCertificate
