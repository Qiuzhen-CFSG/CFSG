module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Transport
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFour.ThompsonGeometry

/-!
# Best offenders on the actual binary natural-plus-dual module

Every best offender on the PSL₄(2) natural-plus-dual representation has
rank four. The first-coordinate submodule is identified with the natural
SL₄(2) action through the actual projective quotient isomorphism; the
second projection identifies its quotient with the contragredient of that
same submodule. These explicit coordinates give the DoubleNatural input
to the proved binary-four geometry theorem of B.4.9(2)(iii).

The source consumer in 15.3.49 compares this rank with the point two-core
bound of three. No representation-classification or splitting premise is
introduced by this module.

Source: Aschbacher--Smith, B.4.9(2)(iii), printed p.92, and 15.3.49,
printed p.1145 (`refs/quasithin.pdf`).
-/

public section
noncomputable section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight

open Subgroup Representation Representation.BinaryOffender
open Chapter2.ComponentRefinement.LieType.Binary
open ChapterB.QuasisimpleSource ChapterB.NaturalExtensions

private def naturalSpace : Subrepresentation (BinaryGeometry.naturalDual 4) where
  toSubmodule := LinearMap.ker (LinearMap.snd (ZMod 2) (Vector 4)
    (Module.Dual (ZMod 2) (Vector 4)))
  apply_mem_toSubmodule g v hv := by
    change (BinaryGeometry.natural 4).dual g v.2 = 0
    rw [show v.2 = 0 from hv, map_zero]

private def naturalSpaceEquiv : naturalSpace.toRepresentation.Equiv (BinaryGeometry.natural 4) where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), rfl⟩
  left_inv v := by apply Subtype.ext; exact Prod.ext rfl v.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

private def naturalQuotientEquiv :
    naturalSpace.quotientRepresentation.Equiv (BinaryGeometry.natural 4).dual :=
  .mk ((LinearMap.snd (ZMod 2) (Vector 4) (Module.Dual (ZMod 2) (Vector 4))).quotKerEquivOfSurjective
    LinearMap.snd_surjective) (by
      intro g
      apply LinearMap.ext
      intro v
      refine Submodule.Quotient.induction_on _ v ?_
      intro w
      rfl)

private def naturalSpaceDualEquiv :
    naturalSpace.toRepresentation.dual.Equiv (BinaryGeometry.natural 4).dual :=
  .mk naturalSpaceEquiv.symm.toLinearEquiv.dualMap (by
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change f (naturalSpace.toRepresentation g⁻¹ (naturalSpaceEquiv.symm w)) =
      f (naturalSpaceEquiv.symm (BinaryGeometry.natural 4 g⁻¹ w))
    exact congrArg f
      (LinearMap.congr_fun (naturalSpaceEquiv.symm.isIntertwining' g⁻¹) w).symm)

private def naturalMarking :
    ActionEquiv (BinaryGeometry.natural 4) (linearNatural BinaryField.two 4) where
  groupEquiv := (slEquivPSL 4).symm
  linearEquiv := LinearEquiv.refl (ZMod 2) (Vector 4)
  intertwines g v := by
    obtain ⟨g,rfl⟩ := (slEquivPSL 4).surjective g
    change BinaryGeometry.natural 4 (slEquivPSL 4 g) v =
      linearNatural BinaryField.two 4 ((slEquivPSL 4).symm (slEquivPSL 4 g)) v
    rw [MulEquiv.symm_apply_apply]
    exact BinaryGeometry.natural_project 4 g v

private theorem natural_faithful : Function.Injective (BinaryGeometry.natural 4) := by
  intro g h he
  apply (pslEquivLinear 4).injective
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun he v

private def naturalDualData : DoubleNatural BinaryField.two 4 (BinaryGeometry.naturalDual 4) where
  faithful := by
    intro g h he
    apply natural_faithful
    apply LinearMap.ext
    intro x
    exact congrArg Prod.fst (LinearMap.congr_fun he (x, 0))
  space := naturalSpace
  natural := {
    groupEquiv := naturalMarking.groupEquiv
    linearEquiv := naturalSpaceEquiv.toLinearEquiv.trans naturalMarking.linearEquiv
    intertwines := by intro g v; exact naturalMarking.intertwines g v.val.1 }
  quotient := Or.inr ⟨naturalQuotientEquiv.trans naturalSpaceDualEquiv.symm⟩

/-- B.4.9(2)(iii) on the actual PSL₄(2) natural-plus-dual coordinates. -/
theorem naturalDualBestRank : NaturalDualBestRank := by
  intro A hA
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  exact (naturalDualData.binary_four_dual_geometry rfl
    (naturalQuotientEquiv.trans naturalSpaceDualEquiv.symm) T hAT hA).2.1

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
