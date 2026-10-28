module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.survivorNodeTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.outputNodeTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.destNodeTable

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

@[expose] public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

def survivor (i : Fin 3125) : Nat := survivorNode i.val

def letterCode (a : Letter (Fin 3)) : Nat := 2 * a.1.val + if a.2 then 0 else 1

def output (i : Fin 3125) (a : Letter (Fin 3)) : Nat :=
  min (outputNode (6 * i.val + letterCode a)) 249177

def dest (i : Fin 3125) (a : Letter (Fin 3)) : Fin 3125 :=
  ⟨min (destNode (6 * i.val + letterCode a)) 3124, by omega⟩

end Lyons.Gebhardt.ParabolicIndexCertificate
