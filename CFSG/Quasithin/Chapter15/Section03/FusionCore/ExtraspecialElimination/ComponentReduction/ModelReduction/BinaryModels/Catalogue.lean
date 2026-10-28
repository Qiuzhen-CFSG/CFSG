module

public import CFSG.Quasithin.ClassicalModels
public import Theory.Representation.HexacodeAction.Cover
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-!
# Concrete targets for the binary component reduction

These alternatives record multiplicative equivalences to the carriers in
15.3.49(l). The linear groups use the actual two-element field, and the G₂
alternative is the derived subgroup of the split-octonion automorphism group.
The even hexacode carrier is a perfect central triple cover of the alternating
group on six letters. Its occurrence in a source module classification still
requires the compatible representation identification; the definition below
asserts no such classification.

This is the shared conclusion language for the model sieve and the component
orbit argument. Parabolic subgroups must be identified under the same group
equivalence in the subsequent geometric argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
clause (l); Appendix A.3.5 and K.1.3 for the triple cover convention and module.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels

/-- The exact group carriers in (l), without any asserted classification or parabolic conclusion. -/
inductive BinaryComponentModel (X : Type*) [Group X] : Prop
  | linear (n : ℕ) (lower : 3 ≤ n) (upper : n ≤ 5)
      (equiv : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
  | alternating_six (equiv : Nonempty (X ≃* alternatingGroup (Fin 6)))
  | triple_cover (equiv : Nonempty (X ≃* Atlas.Codes.HexEvenAutomorphisms))
  | alternating_seven (equiv : Nonempty (X ≃* alternatingGroup (Fin 7)))
  | g2_derived (equiv : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- Change the presentation of the component by composing actual equivalences. -/
theorem BinaryComponentModel.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (h : BinaryComponentModel X) (e : Y ≃* X) : BinaryComponentModel Y := by
  cases h with
  | linear n lo hi iso => exact .linear n lo hi (iso.map (e.trans ·))
  | alternating_six iso => exact .alternating_six (iso.map (e.trans ·))
  | triple_cover iso => exact .triple_cover (iso.map (e.trans ·))
  | alternating_seven iso => exact .alternating_seven (iso.map (e.trans ·))
  | g2_derived iso => exact .g2_derived (iso.map (e.trans ·))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
