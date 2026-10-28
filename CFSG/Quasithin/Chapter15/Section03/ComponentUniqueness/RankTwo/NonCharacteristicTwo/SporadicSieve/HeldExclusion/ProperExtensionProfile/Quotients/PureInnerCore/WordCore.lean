module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Structure
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair00
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# A concrete normal two-subgroup of Held's pure pair product

The eight existing residual words generate a normal two-subgroup of the literal
pair product B. Normality is checked in B using its six defining generators;
the residual-core containment supplies the two-group property. We retain the
canonical conjugation action of B on the center of this word subgroup. Counting
its image is a separate finite model calculation, not an assumption identifying
B with an abstract group.

Sources: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
the unchanged ATLAS pair words and the certified ResidualRoots relations.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry

private theorem word_le_residualCore : ResidualRoots.group false 0 ≤ pairTwoCore false 0 :=
  ResidualRoots.group_le_pairTwoCore_of_relations false 0 ResidualRoots.Pair00.fourth
    ResidualRoots.Pair00.internal ResidualRoots.Pair00.conjugate

theorem pureWordGroup_le : ResidualRoots.group false 0 ≤ innerLocal true :=
  word_le_residualCore.trans (pairTwoCore_le_pairProduct false 0)

def pureWordCore : Subgroup (innerLocal true) :=
  (ResidualRoots.group false 0).subgroupOf (innerLocal true)

instance pureWordCore_normal : pureWordCore.Normal := by
  apply (normal_subgroupOf_iff_le_normalizer pureWordGroup_le).mpr
  apply ResidualRoots.pairProduct_le_of_generators false 0
  intro k
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨l, rfl⟩
  rw [ResidualRoots.Pair00.conjugate]
  exact ResidualRoots.product_mem_group false 0 _

theorem pureWordCore_isPGroup : IsPGroup 2 pureWordCore := by
  have hp : IsPGroup 2 (pairTwoCore false 0) := pCore_isPGroup.map _
  have hg := hp.of_injective (inclusion word_le_residualCore)
    (inclusion_injective word_le_residualCore)
  exact hg.of_equiv (subgroupOfEquivOfLe pureWordGroup_le).symm

theorem pureWordCore_le_pCore : pureWordCore ≤ pCore 2 (innerLocal true) :=
  le_sSup ⟨inferInstance, pureWordCore_isPGroup⟩

def pureCenterAction : innerLocal true →* MulAut (center pureWordCore) :=
  (MulAut.characteristic (center pureWordCore)).comp (MulAut.conjNormal (H := pureWordCore))

theorem pureCenterAction_apply (g : innerLocal true) (z : center pureWordCore) :
    ((pureCenterAction g z : pureWordCore) : innerLocal true) =
      g * (z : pureWordCore) * g⁻¹ := rfl

/-- The word subgroup acts trivially on its own center. -/
theorem pureWordCore_le_centerAction_kernel : pureWordCore ≤ pureCenterAction.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change x * (z : pureWordCore) * x⁻¹ = (z : pureWordCore)
  have he := congrArg Subtype.val (z.property.comm (⟨x, hx⟩ : pureWordCore))
  change (z : pureWordCore).val * x = x * (z : pureWordCore).val at he
  rw [← he, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
