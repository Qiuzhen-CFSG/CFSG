module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Base

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def relatorFin : Fin 9 → Word (Fin 3) := fun i => match i.val with
  | 0 => [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]
  | 1 => [(1, true), (1, true), (1, true), (1, true), (1, true)]
  | 2 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]
  | 3 => [(0, false), (0, false), (1, false), (0, true), (0, true), (1, true)]
  | 4 => [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)]
  | 5 => [(2, true), (2, true), (2, true), (2, true), (2, true)]
  | 6 => [(0, false), (0, false), (2, true), (0, true), (0, true), (2, false), (2, false), (2, false)]
  | 7 => [(0, false), (1, false), (2, true), (1, true), (0, true), (1, true), (2, false), (1, false), (2, false), (1, false), (0, false), (0, false), (2, false), (0, true), (0, true), (1, true)]
  | 8 => [(1, false), (1, false), (2, true), (1, true), (2, true), (2, true), (1, true), (1, true), (2, false), (1, false), (2, false), (2, false)]
  | _ => []

def relatorWords (r : Nat) : Word (Fin 3) :=
  if h : r < 9 then relatorFin ⟨r, h⟩ else []

end Lyons.Gebhardt.ParabolicIndexCertificate
