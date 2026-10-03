module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02Part00
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02Part01
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02Part02
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02Part03
/-!
# Exact extensions of node 2

The checked row intervals are assembled into exact representation of every
extension in the certified right-coset cover. Words in both directions certify
proper targets; ambient generation certifies the actual whole-group targets.
Source: `SubgroupEnumeration.ExtensionWords.sound` and GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions02
open Theory.GroupTheory.SubgroupEnumeration CosetCheck ExtensionCheck
public theorem represented (j : Fin 1872) :
    Represented node (properNode 2 ⊔ Subgroup.zpowers (Cosets02.rep j)) := by
  apply ExtensionCheck.sound 2 _ (witness j)
  exact checkRange_fin (by decide) (fun j => check (nodeGenerator 2)
    (Cosets02.rep j) (witness j)) (@checkRange_append rowCheck 0 1024 848 (@checkRange_append rowCheck 0 512 512 checkedPart0 checkedPart1) (@checkRange_append rowCheck 1024 512 336 checkedPart2 checkedPart3)) j
end Matrix.PSL3Three.CertifiedEnumeration.Extensions02
