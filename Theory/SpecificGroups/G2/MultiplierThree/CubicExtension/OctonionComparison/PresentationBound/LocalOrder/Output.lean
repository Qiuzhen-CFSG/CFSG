module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.survivorNodeTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.outputNodeTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.destNodeTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

def survivor : Fin 1296 → Nat := fun i => survivorNode i.val

def letterCode (a : Letter (Bool)) : Nat :=
  2 * (if a.1 then 1 else 0) + if a.2 then 0 else 1

def output (i : Fin 1296) (a : Letter (Bool)) : Nat :=
  min (outputNode (4 * i.val + letterCode a)) 85575

def dest (i : Fin 1296) (a : Letter (Bool)) : Fin 1296 :=
  ⟨min (destNode (4 * i.val + letterCode a)) 1295, by omega⟩

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
