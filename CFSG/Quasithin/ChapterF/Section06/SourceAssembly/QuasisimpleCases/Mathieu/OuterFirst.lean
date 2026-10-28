module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import Theory.GroupTheory.Amalgam.DihedralTwelvePair.Models

/-!
# The quaternion denominator in the first Aut(M₁₂) vertex

The actual quaternion core is the intersection of the first two-core with
the marked inner M₁₂. The two quotient maps, to the outer C₂ and to the
existing S₃ quotient, therefore have this exact common kernel. Orders make
their product surjective, giving the actual D₁₂ quotient. The kernel retains
its two embedded quaternion factors, as required by F.6.18(13).

Source: Aschbacher–Smith, F.6.18(13), printed p.310; marked local calculations
in F.1.12(13) and 14.2.21. No splitting of the quaternion extension is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterFirst

@[expose] def quaternionKernel : Subgroup firstParabolic :=
  quaternionCore.subgroupOf firstParabolic
instance : quaternionKernel.Normal := quaternionCore_normal_firstParabolic innerModel

def quaternionKernelData : QuaternionCentralProductData quaternionKernel :=
  (quaternionData innerModel).map
    (subgroupOfEquivOfLe (quaternionCore_le_firstParabolic innerModel)).symm

theorem quaternionKernel_card : Nat.card quaternionKernel = 32 := quaternionKernelData.card

private def innerKernel : Subgroup firstParabolic := inner.subgroupOf firstParabolic
private instance : innerKernel.Normal := normal_of_index_eq_two (inner_firstParabolic_index innerModel)

private def outerQuotient : (firstParabolic ⧸ innerKernel) ≃*
    RankTwoAmalgam.swapMiddle :=
  mulEquivOfPrimeCardEq (p := 2) (inner_firstParabolic_index innerModel)
    RankTwoAmalgam.swapMiddle_card

private def outerMap : firstParabolic →* RankTwoAmalgam.swapMiddle :=
  outerQuotient.toMonoidHom.comp (QuotientGroup.mk' innerKernel)

private theorem outerMap_ker : outerMap.ker = innerKernel := by
  ext x
  change outerQuotient (QuotientGroup.mk' innerKernel x) = 1 ↔ x ∈ innerKernel
  rw [outerQuotient.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private def symmetricMap : firstParabolic →* Equiv.Perm (Fin 3) :=
  (firstParabolicPcoreQuotient innerModel).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 firstParabolic))

private theorem symmetricMap_ker : symmetricMap.ker = pCore 2 firstParabolic := by
  ext x
  change firstParabolicPcoreQuotient innerModel
    (QuotientGroup.mk' (pCore 2 firstParabolic) x) = 1 ↔ x ∈ pCore 2 firstParabolic
  rw [(firstParabolicPcoreQuotient innerModel).map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private def productMap : firstParabolic →* RankTwoAmalgam.DihedralTwelveVertex :=
  outerMap.prod symmetricMap

private theorem productMap_ker : productMap.ker = quaternionKernel := by
  rw [productMap, MonoidHom.ker_prod, outerMap_ker, symmetricMap_ker,
    ← outerCore_subgroupOf_eq_pCore innerModel]
  ext x
  change (x : Carrier) ∈ M12ExceptionalExtension.inner ∧ (x : Carrier) ∈ outerCore ↔ (x : Carrier) ∈ quaternionCore
  rw [← outerCore_inf_inner innerModel]
  exact and_comm

private theorem productMap_surjective : Function.Surjective productMap := by
  have hc := productMap.ker.card_mul_index
  rw [productMap_ker, quaternionKernel_card, card_firstParabolic innerModel] at hc
  have hi : productMap.ker.index = 12 := by rw [productMap_ker]; omega
  have hr : Nat.card productMap.range = 12 := by rwa [← index_ker]
  have htarget : Nat.card RankTwoAmalgam.DihedralTwelveVertex = 12 := by
    rw [Nat.card_congr RankTwoAmalgam.dihedralTwelveVertexEquiv.toEquiv,
      DihedralGroup.nat_card]
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_of_le_of_card_ge le_top
  rw [card_top, htarget, hr]

/-- The actual first Aut(M₁₂) vertex modulo its quaternion central product is D₁₂. -/
def firstQuotientEquiv : (firstParabolic ⧸ quaternionKernel) ≃* DihedralGroup 6 :=
  (QuotientGroup.quotientMulEquivOfEq productMap_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective productMap productMap_surjective).trans
      RankTwoAmalgam.dihedralTwelveVertexEquiv)

/-- The full first-vertex extension assertion of row (13), with literal denominator. -/
theorem first_extension : ∃ N : Subgroup firstParabolic, ∃ _ : N.Normal,
    Nonempty (QuaternionCentralProductData N) ∧
      Nonempty ((firstParabolic ⧸ N) ≃* DihedralGroup 6) :=
  ⟨quaternionKernel, inferInstance, ⟨quaternionKernelData⟩, ⟨firstQuotientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterFirst
