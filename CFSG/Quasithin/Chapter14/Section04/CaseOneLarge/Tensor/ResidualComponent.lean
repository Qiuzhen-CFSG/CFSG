module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.Residual
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.AlternatingFiveCore
/-!
# The genuine component behind the tensor marking

The literal image of H∞ in H/O₂(H) is A₅. The two-group kernel transport
identifies H∞/O₂(H∞) with that same A₅. Perfectness of the solvable residual
then proves that it is a C-component relative to H.

This supplies local-family membership in the deleted-tensor core split.
No ambient normality or equality of U and O₂(H) is assumed.
Source: Aschbacher--Smith 14.4.10(1),(3), printed pp.1010--1011.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
open LargerDimension LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

/-- The component quotient, transported through the original star image. -/
noncomputable def componentQuotient (e : star H (component H) ≃* AltFive) :
    coreQuotient (component H) ≃* AltFive :=
  (starCoreQuotientEquiv (map_subtype_le _)).trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
        QuotientGroup.quotientBot))

/-- The marked residual is an actual C-component of H. -/
theorem component_isCComponent (e : star H (component H) ≃* AltFive) :
    ((component H).subgroupOf H).IsCComponent := by
  let K := component H
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective |>.toMonoidHom)
    ((solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective).surjective
  let : IsSimpleGroup AltFive := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect AltFive := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple AltFive := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let q := componentQuotient e
  let : IsQuasisimple (coreQuotient K) := IsQuasisimple.of_mulEquiv q.symm
  let k := subgroupOfEquivOfLe (show K ≤ H from map_subtype_le _)
  let : Group.IsPerfect (K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := k.symm.toMonoidHom) k.symm.surjective
  let q' := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q'.symm
  have hn : (K.subgroupOf H).Normal := by
    change (((solvableResidual H).map H.subtype).subgroupOf H).Normal
    rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hp
    let := hN
    by_contra hne
    let : Nontrivial ((K.subgroupOf H) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((K.subgroupOf H) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((K.subgroupOf H) ⧸ N) inferInstance
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal hp
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.TensorDeleted
