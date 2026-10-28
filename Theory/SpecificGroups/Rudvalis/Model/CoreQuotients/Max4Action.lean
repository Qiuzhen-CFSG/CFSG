module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightAction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Conjugation of the Rudvalis max4 subgroup on its marked eight-group

The checked max4 generator identities normalize the literal subgroup
`LocalCover.elementary 2`. Restrict its normalizer homomorphism to max4.
Its kernel is exactly the centralizer of this subgroup inside max4.
The checked elementary abelian structure and order eight identify its
automorphism group with GL₃(2), and hence with the binary matrix PSL₃(2).

This constructs the actual action but does not claim it is surjective.
Surjectivity is the remaining image calculation; combined with the local
order it will identify the centralizer kernel with the intrinsic two-core.
Source: GLS3 Table 5.3r and its max4 justification, printed pp.291–292.
All word and point-action conventions are inherited from the cited ATLAS
certificates in `SylowOvergroups.Definitions` and `LocalCover.Data`.
-/

namespace Rudvalis.CoreQuotients

open Subgroup SylowOvergroups
open SylowOvergroups.RadicalCoverage.LocalCover

/-- The actual conjugation action on the marked elementary subgroup of order eight. -/
@[expose] public def max4EightAction : max4 →* MulAut (elementary 2) :=
  (elementary 2).normalizerMonoidHom.comp
    (Subgroup.inclusion RankOneEightAction.max4_le_normalizer_eight)

/-- The action uses the same left-conjugation convention as the checked word identities. -/
@[simp] public theorem max4EightAction_apply (g : max4) (x : elementary 2) :
    (max4EightAction g x : Model) = (g : Model) * (x : Model) * (g : Model)⁻¹ := rfl

/-- The action kernel is the relative centralizer, not an ambient normal subgroup. -/
public theorem max4EightAction_ker :
    max4EightAction.ker = (centralizer (elementary 2 : Set Model)).subgroupOf max4 := by
  rw [max4EightAction, ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

/-- The full automorphism group of the marked eight-group in the binary matrix model. -/
public noncomputable def eightAutEquivPSL :
    MulAut (elementary 2) ≃* Matrix.PSL3Two.PSL := by
  letI := RankOneEightCharacteristic.elementary_two_elementary
  exact (elementaryEight_mulAut_equiv_GL (elementary 2)
    RankOneEightCharacteristic.elementary_two_card).some.trans
      (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)

/-- The actual conjugation action, expressed in the project's PSL₃(2) model. -/
@[expose] public noncomputable def max4LinearAction : max4 →* Matrix.PSL3Two.PSL :=
  eightAutEquivPSL.toMonoidHom.comp max4EightAction

/-- Expressing the same action in matrices does not change its kernel. -/
public theorem max4LinearAction_ker : max4LinearAction.ker = max4EightAction.ker := by
  ext g
  change eightAutEquivPSL (max4EightAction g) = 1 ↔ max4EightAction g = 1
  rw [← eightAutEquivPSL.map_one, eightAutEquivPSL.injective.eq_iff]

/-- Full image of the marked eight-group action supplies the required matrix surjection. -/
public theorem max4LinearAction_surjective_of_eightAction
    (h : Function.Surjective max4EightAction) : Function.Surjective max4LinearAction :=
  eightAutEquivPSL.surjective.comp h

end Rudvalis.CoreQuotients
