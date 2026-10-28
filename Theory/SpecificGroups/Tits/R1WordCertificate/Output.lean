module

public import Theory.SpecificGroups.Tits.R1WordCertificate.survivorNodeTable
public import Theory.SpecificGroups.Tits.R1WordCertificate.outputNodeTable
public import Theory.SpecificGroups.Tits.R1WordCertificate.destNodeTable

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

@[expose] public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

def survivor : Fin 1024 → Nat := fun i => survivorNode i.val

def letterCode : Letter ParrottR1Generator → Nat
  | (.r1, true) => 0
  | (.r1, false) => 1
  | (.s1, true) => 2
  | (.s1, false) => 3
  | (.s2, true) => 4
  | (.s2, false) => 5
  | (.s3, true) => 6
  | (.s3, false) => 7
  | (.s4, true) => 8
  | (.s4, false) => 9
  | (.s5, true) => 10
  | (.s5, false) => 11
  | (.s6, true) => 12
  | (.s6, false) => 13
  | (.s7, true) => 14
  | (.s7, false) => 15
  | (.s8, true) => 16
  | (.s8, false) => 17

def output (i : Fin 1024) (a : Letter ParrottR1Generator) : Nat :=
  min (outputNode (18 * i.val + letterCode a)) 304876

def dest (i : Fin 1024) (a : Letter ParrottR1Generator) : Fin 1024 :=
  ⟨min (destNode (18 * i.val + letterCode a)) 1023, by omega⟩

end Tits.R1WordCertificate
