module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.survivorNodeTable
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.outputNodeTable
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.destNodeTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

def survivor : Fin 48 → Nat := fun i => survivorNode i.val

def letterCode (a : Letter (Fin 3)) : Nat :=
  2 * a.1.val + if a.2 then 0 else 1

def output (i : Fin 48) (a : Letter (Fin 3)) : Nat :=
  min (outputNode (6 * i.val + letterCode a)) 7999

def dest (i : Fin 48) (a : Letter (Fin 3)) : Fin 48 :=
  ⟨min (destNode (6 * i.val + letterCode a)) 47, by omega⟩

end G2Five.AtlasPresentation.ThirtyCertificate
