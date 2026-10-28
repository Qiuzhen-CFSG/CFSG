module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.opCodeTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Context

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def instructions (n : Nat) : Instruction (Fin 3) :=
  let c := opCode n
  let a := c / 8 % 262144
  let b := c / 2097152
  match c % 8 with
  | 0 => .refl a
  | 1 => .defining a
  | 2 => .subgroup (decode a)
  | 3 => .relator a b
  | 4 => .reverse a
  | _ => .compose a b

end Lyons.Gebhardt.ParabolicIndexCertificate
