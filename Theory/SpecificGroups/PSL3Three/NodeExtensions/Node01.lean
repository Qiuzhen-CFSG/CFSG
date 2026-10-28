module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part00
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part01
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part02
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part03
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part04
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01Part05
/-!
# Exact extensions of node 1

The checked row intervals are assembled into exact representation of every
extension in the certified right-coset cover. Words in both directions certify
proper targets; ambient generation certifies the actual whole-group targets.
Source: `SubgroupEnumeration.ExtensionWords.sound` and GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions01
open Theory.GroupTheory.SubgroupEnumeration CosetCheck ExtensionCheck
public theorem represented (j : Fin 2808) :
    Represented node (properNode 1 ⊔ Subgroup.zpowers (Cosets01.rep j)) := by
  apply ExtensionCheck.sound 1 _ (witness j)
  exact checkRange_fin (by decide) (fun j => check (nodeGenerator 1)
    (Cosets01.rep j) (witness j)) (@checkRange_append rowCheck 0 1536 1272 (@checkRange_append rowCheck 0 512 1024 checkedPart0 (@checkRange_append rowCheck 512 512 512 checkedPart1 checkedPart2)) (@checkRange_append rowCheck 1536 512 760 checkedPart3 (@checkRange_append rowCheck 2048 512 248 checkedPart4 checkedPart5))) j
end Matrix.PSL3Three.CertifiedEnumeration.Extensions01
