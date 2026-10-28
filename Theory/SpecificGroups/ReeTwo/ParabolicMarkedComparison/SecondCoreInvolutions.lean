module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCensus

/-!
# Involutions in the native second core

A packed kernel certificate counts the order-two elements in all 2,048 core
coordinates. The total is 79, smaller than the full middle's 143. This is the
source involution-escape invariant for the F.1.12 second-endpoint alternatives.
-/

public section
noncomputable section
namespace ReeTwo.SylowModel.CollectedBitVectors

open CubicAction

private def involutionMask : BitVec 2048 :=
  equal (product coreEnumeration coreEnumeration) (pack 1) &&& ~~~(equal coreEnumeration (pack 1))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem core_involution_count_check : involutionMask.cpopNatRec 2048 0=79 := by decide +kernel

/-- The second core has exactly seventy-nine involutions. -/
theorem core_involution_card : Nat.card {a:A // orderOf a=2}=79 := by
  let e : {k:Fin 2048 // involutionMask.getLsbD k.val=true}≃{a:A // orderOf a=2} :=
    Equiv.subtypeEquiv coreEnumerationEquiv (fun k=>by
      rw [orderOf_eq_prime_iff]
      simp only [involutionMask,BitVec.getLsbD_and,BitVec.getLsbD_not,k.isLt,decide_true,
        Bool.true_and,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
        equal_spec,read_product,read_pack,read_coreEnumeration]
      have hcoe (a:A):(a:SylowModel)=1 ↔ a=1 :=
        ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
      simp only [←Subgroup.coe_mul,hcoe,pow_two])
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype,pop_card,core_involution_count_check]


end ReeTwo.SylowModel.CollectedBitVectors
