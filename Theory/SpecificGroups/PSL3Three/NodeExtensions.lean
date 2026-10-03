module
public import Theory.SpecificGroups.PSL3Three.CosetCover
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node00
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node01
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node02
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node03
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node04
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node05
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node06
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node07
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node08
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node09
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node10
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node11
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node12
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node13
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node14
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node15
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node16
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node17
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node18
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node19
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node20
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node21
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node22
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node23
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node24
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node25
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node26
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node27
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node28
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node29
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node30
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node31
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node32
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node33
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node34
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node35
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node36
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node37
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node38
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node39
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node40
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node41
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node42
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node43
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node44
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node45
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node46
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node47
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node48
public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Node49

/-!
# Closure of the fixed SL₃(3) subgroup family under extensions

For every fixed proper node, every representative of its certified right-coset
cover has an exact extension certificate. Proper targets are identified by
conjugation and word witnesses for both containments. Whole-group targets are
proved using words for the ambient generators and their generation theorem.
The right-coset factorization then reduces an arbitrary extension to a checked
row. Node zero is bottom and node fifty is the actual whole matrix group.

The 51 nodes, including the two distinct order-24 nodes, are exactly those in
`RepresentativeBounds`. External subgroup search supplies only word witnesses;
neither subgroup orders nor an external classification enter this proof.

Source: the one-generator extension induction in `SubgroupEnumeration`, applied
to the concrete matrices for GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration
open Theory.GroupTheory.SubgroupEnumeration

/-- Every certified right-coset representative has an exactly represented extension. -/
public theorem properNode_extension_represented (i : Fin 50)
    (r : Fin (cosetCount i)) :
    Represented node (properNode i ⊔ Subgroup.zpowers (cosetRepresentative i r)) := by
  fin_cases i
  · exact Extensions00.represented r
  · exact Extensions01.represented r
  · exact Extensions02.represented r
  · exact Extensions03.represented r
  · exact Extensions04.represented r
  · exact Extensions05.represented r
  · exact Extensions06.represented r
  · exact Extensions07.represented r
  · exact Extensions08.represented r
  · exact Extensions09.represented r
  · exact Extensions10.represented r
  · exact Extensions11.represented r
  · exact Extensions12.represented r
  · exact Extensions13.represented r
  · exact Extensions14.represented r
  · exact Extensions15.represented r
  · exact Extensions16.represented r
  · exact Extensions17.represented r
  · exact Extensions18.represented r
  · exact Extensions19.represented r
  · exact Extensions20.represented r
  · exact Extensions21.represented r
  · exact Extensions22.represented r
  · exact Extensions23.represented r
  · exact Extensions24.represented r
  · exact Extensions25.represented r
  · exact Extensions26.represented r
  · exact Extensions27.represented r
  · exact Extensions28.represented r
  · exact Extensions29.represented r
  · exact Extensions30.represented r
  · exact Extensions31.represented r
  · exact Extensions32.represented r
  · exact Extensions33.represented r
  · exact Extensions34.represented r
  · exact Extensions35.represented r
  · exact Extensions36.represented r
  · exact Extensions37.represented r
  · exact Extensions38.represented r
  · exact Extensions39.represented r
  · exact Extensions40.represented r
  · exact Extensions41.represented r
  · exact Extensions42.represented r
  · exact Extensions43.represented r
  · exact Extensions44.represented r
  · exact Extensions45.represented r
  · exact Extensions46.represented r
  · exact Extensions47.represented r
  · exact Extensions48.represented r
  · exact Extensions49.represented r

/-- The exact fixed family is closed under every one-generator extension. -/
public theorem node_extensionClosed : ExtensionClosed node := by
  refine ⟨⟨0, node_zero⟩, fun i x => ?_⟩
  by_cases hi : i.val < 50
  · have hn : node i = properNode ⟨i.val, hi⟩ := dif_pos hi
    rw [hn]
    obtain ⟨r, a, ha, hx⟩ := rightCosetCover ⟨i.val, hi⟩ x
    rw [hx, extension_mul_left _ ha]
    exact properNode_extension_represented ⟨i.val, hi⟩ r
  · exact ⟨50, 1, by simp [node, hi]⟩

end Matrix.PSL3Three.CertifiedEnumeration
