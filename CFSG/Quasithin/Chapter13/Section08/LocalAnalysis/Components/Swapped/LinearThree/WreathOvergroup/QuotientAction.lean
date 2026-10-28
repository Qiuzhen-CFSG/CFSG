module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Points
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Automizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Image
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Kernel
public import Theory.GroupTheory.PCoreSurjective

/-!
# Parabolic core actions and the full overlap automizer

`ParabolicPair.corePointAction` is literal conjugation on the six nonidentity
core elements; `liftedCorePointAction` pulls it back to the full overgroup.
The surjective lift has two-group kernel and preserves the action image.
The two-block embedding and image order 72 identify that image with the
concrete wreath model. Its trivial two-core makes the action kernel exactly
the intrinsic two-core, first in the star overgroup and then in its full lift.
`ParabolicPair.twoBlockQuotientData` packages the resulting literal action;
`ParabolicPair.overgroupQuotientEquiv` constructs the required wreath quotient
from the parabolic pair alone.

`automizer_range_eq` and `automizerEquivDihedral` prove the independent
full-automizer comparison from an actual wreath quotient, residual marking,
shared Sylow subgroup and the source bound excluding 27 from |H|.

These deductions support the L₃(2) branch in Aschbacher–Smith 13.8.16(1),
printed p.952. The source assembly must still select the parabolic pair
and discharge the residual, numerical and Sylow premises of the automizer
comparison.
-/


public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
open WreathModel

/-- The normal self-centralizing cubic base excludes every normal two-subgroup. -/
theorem wreathModel_twoCore_eq_bot : pCore 2 W = ⊥ := by
  have hd : Disjoint (pCore 2 W) cubicBase :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
      (IsElementaryAbelian.isPGroup 3 cubicBase)
  have hc : pCore 2 W ≤ centralizer (cubicBase : Set W) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  apply le_bot_iff.mp
  intro x hx
  have hk : x ∈ WreathModel.action.ker := by
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change x * (y : W) * x⁻¹ = y
    rw [← mem_centralizer_iff.mp (hc hx) y y.property, mul_inv_cancel_right]
  rw [WreathModel.action_kernel] at hk
  exact mem_bot.mpr (Subgroup.disjoint_def.mp hd hx hk)

private noncomputable def permutationWreathEquiv : S3Wreath ≃* W :=
  RegularWreathProduct.congr
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
    (MulEquiv.refl C2)

private theorem s3Wreath_card : Nat.card S3Wreath = 72 := by
  rw [Nat.card_congr (RegularWreathProduct.equivProd _ _), Nat.card_prod,
    Nat.card_fun, Nat.card_perm]
  norm_num [C2, Nat.factorial]

private theorem model_card : Nat.card W = 72 :=
  (Nat.card_congr permutationWreathEquiv.symm.toEquiv).trans s3Wreath_card

namespace ParabolicPair
variable {G : Type*} [Group G] [Finite G] {H L₁ T : Subgroup G} (d : ParabolicPair H L₁ T)

/-- The literal six-point image is the full wreath group: its block embedding
is surjective because both groups have the computed order 72. -/
noncomputable def corePointAction_rangeEquivModel : d.corePointAction.range ≃* W := by
  let hex := RegularWreathProduct.exists_embedding_range_of_two_blocks
    d.corePointAction d.corePointLabels d.corePointAction_blocks
  let f := Classical.choose hex
  have hf := Classical.choose_spec hex
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, d.corePointAction_range_card.trans model_card.symm⟩)

/-- The actual permutation image has no nontrivial normal two-subgroup. -/
theorem corePointAction_range_twoCore_eq_bot : pCore 2 d.corePointAction.range = ⊥ := by
  have h := pCore_map_iso 2 d.corePointAction_rangeEquivModel.symm
  rw [wreathModel_twoCore_eq_bot, Subgroup.map_bot] at h
  exact h.symm

/-- The two-group point kernel is the entire two-core of the star overgroup. -/
theorem corePointAction_kernel_eq_core : d.corePointAction.ker = pCore 2 d.starOvergroup := by
  have hk : IsPGroup 2 d.corePointAction.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact d.corePointAction_kernel_isPGroup
  have h := d.corePointAction.rangeRestrict.comap_pCore_of_ker_isPGroup
    d.corePointAction.rangeRestrict_surjective hk
  rw [d.corePointAction_range_twoCore_eq_bot] at h
  change d.corePointAction.rangeRestrict.ker = pCore 2 d.starOvergroup at h
  rwa [MonoidHom.ker_rangeRestrict] at h

/-- Pulling back through the full lift identifies the literal action kernel
with the intrinsic O₂(H₁), rather than merely the original O₂(H). -/
theorem liftedCorePointAction_kernel_eq_core :
    d.liftedCorePointAction.ker = pCore 2 d.overgroup := by
  change d.corePointAction.ker.comap d.starProjection = pCore 2 d.overgroup
  rw [d.corePointAction_kernel_eq_core]
  exact d.starProjection.comap_pCore_of_ker_isPGroup
    d.starProjection_surjective d.starProjection_kernel_isPGroup

/-- The order of H₁/O₂(H₁) follows from the literal action image. -/
theorem overgroup_quotient_card : Nat.card (d.overgroup ⧸ pCore 2 d.overgroup) = 72 := by
  rw [← d.liftedCorePointAction_kernel_eq_core,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange d.liftedCorePointAction).toEquiv]
  exact d.liftedCorePointAction_range_card

/-- The parabolic geometry discharges every field of the two-block interface. -/
noncomputable def twoBlockQuotientData : TwoBlockQuotientData (H₁ := d.overgroup) where
  X := d.CorePoints
  action := d.liftedCorePointAction
  labels := d.corePointLabels
  block_preserved := d.liftedCorePointAction_blocks
  kernel_eq_core := d.liftedCorePointAction_kernel_eq_core
  quotient_card := d.overgroup_quotient_card.trans s3Wreath_card.symm

/-- The full lifted overgroup modulo its intrinsic two-core is the concrete
SL₂(2) wreath C₂ model, constructed from the marked parabolic pair alone. -/
noncomputable def overgroupQuotientEquiv : d.overgroup ⧸ pCore 2 d.overgroup ≃* W :=
  d.twoBlockQuotientData.quotientEquiv.trans permutationWreathEquiv

end ParabolicPair

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
end
