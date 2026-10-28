module
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part00
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part01
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part02
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part03
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part04
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part05
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part06
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part07
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part08
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part09
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00Part10
/-!
# Exact extensions of node 0

The checked row intervals are assembled into exact representation of every
extension in the certified right-coset cover. Words in both directions certify
proper targets; ambient generation certifies the actual whole-group targets.
Source: `SubgroupEnumeration.ExtensionWords.sound` and GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.Extensions00
open Theory.GroupTheory.SubgroupEnumeration CosetCheck ExtensionCheck
public theorem represented (j : Fin 5616) :
    Represented node (properNode 0 ⊔ Subgroup.zpowers (Cosets00.rep j)) := by
  apply ExtensionCheck.sound 0 _ (witness j)
  exact checkRange_fin (by decide) (fun j => check (nodeGenerator 0)
    (Cosets00.rep j) (witness j)) (@checkRange_append rowCheck 0 2560 3056 (@checkRange_append rowCheck 0 1024 1536 (@checkRange_append rowCheck 0 512 512 checkedPart0 checkedPart1) (@checkRange_append rowCheck 1024 512 1024 checkedPart2 (@checkRange_append rowCheck 1536 512 512 checkedPart3 checkedPart4))) (@checkRange_append rowCheck 2560 1536 1520 (@checkRange_append rowCheck 2560 512 1024 checkedPart5 (@checkRange_append rowCheck 3072 512 512 checkedPart6 checkedPart7)) (@checkRange_append rowCheck 4096 512 1008 checkedPart8 (@checkRange_append rowCheck 4608 512 496 checkedPart9 checkedPart10)))) j
end Matrix.PSL3Three.CertifiedEnumeration.Extensions00
