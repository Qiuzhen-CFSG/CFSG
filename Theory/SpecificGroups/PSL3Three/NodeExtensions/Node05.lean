module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node05Part00
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node05Part01
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node05Part02
/-!
# Exact extensions of node 5

The checked row intervals are assembled into exact representation of every
extension in the certified right-coset cover. Words in both directions certify
proper targets; ambient generation certifies the actual whole-group targets.
Source: `SubgroupEnumeration.ExtensionWords.sound` and GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions05
open Theory.GroupTheory.SubgroupEnumeration CosetCheck ExtensionCheck
public theorem represented (j : Fin 1404) :
    Represented node (properNode 5 ⊔ Subgroup.zpowers (Cosets05.rep j)) := by
  apply ExtensionCheck.sound 5 _ (witness j)
  exact checkRange_fin (by decide) (fun j => check (nodeGenerator 5)
    (Cosets05.rep j) (witness j)) (@checkRange_append rowCheck 0 512 892 checkedPart0 (@checkRange_append rowCheck 512 512 380 checkedPart1 checkedPart2)) j
end Matrix.PSL3Three.CertifiedEnumeration.Extensions05
