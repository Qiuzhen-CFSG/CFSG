module
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.SL2.BinaryThreeSection

/-!
# The binary-three obstruction in binary triality

A proper perfect subgroup normalized by a full Sylow of ³D₄(2) has its
actual image in the arms local factor. That factor has SL₂(8) quotient
by its two-core. The order-four element in an SL₃(2) quotient rules out
this embedding, using the literal inclusion and its two-group kernel.
This argument does not require perfectness of the whole arms factor.

Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751.
The point-control consumer is RankTwo.BinaryThree.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Triality.Standard.BinaryLocalSections
open Parabolics

/-- A proper perfect subgroup normalized by a full Sylow of binary triality
cannot have an SL₃(2) quotient. The arm marking is the actual inclusion. -/
theorem no_binary_three_quotient_of_normalized
    (S : Sylow 2 (BinaryCarrier 1 Nat.zero_lt_one))
    (B : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) [Group.IsPerfect B]
    (hne : B ≠ ⊤) (hns : ¬ Group.IsSolvable B)
    (hn : (S : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) ≤
      normalizer (B : Set (BinaryCarrier 1 Nat.zero_lt_one)))
    (π : B →* SL(3,ZMod 2)) (hπ : Function.Surjective π) : False := by
  obtain ⟨a,_,hBL,_,_⟩ := marked_arm_quotient (MulEquiv.refl _) S B hne hns hn
  let f := (inclusion hBL).comp (a.subgroupMap B).toMonoidHom
  have hf : Function.Injective f := (inclusion_injective hBL).comp
    (a.subgroupMap B).injective
  have hk : IsPGroup 2 f.ker := by
    rw [f.ker_eq_bot_iff.mpr hf]
    exact IsPGroup.of_card (n := 0) (by simp)
  let P := binaryParameters 1 Nat.zero_lt_one
  exact Matrix.SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient π hπ f hk
    ((localFactorArmsQuotientEquivPSL2 P rfl).trans
      (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm)

end Triality.Standard.BinaryLocalSections
