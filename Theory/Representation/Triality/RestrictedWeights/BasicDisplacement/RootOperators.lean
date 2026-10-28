module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.Weyl

/-!
# The two concrete triality root involutions and Weyl representatives

In characteristic two the central root element, and the product of the
three commuting arm root elements, are conjugate to the corresponding
simple Weyl representatives. The conjugators are the opposite root points
with parameter one. We verify three short coordinate actions in the faithful
natural Spin action, then lift the identities to the actual Spin carrier.
The split coordinate calculations avoid expanding nine root operators at once.

These literal conjugacies transfer the exchanged-weight displacement bounds
to the marked long and short root operators, including the binary field case.
Source: GLS3 1.12.1, with the repository's central vertex numbered one.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
namespace Triality.RestrictedWeights.BasicDisplacement
noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def rootOperator (short : Bool) : Points k :=
  if short then rootPoint k (simpleRoot 0) 1 * rootPoint k (simpleRoot 2) 1 *
    rootPoint k (simpleRoot 3) 1 else rootPoint k (simpleRoot 1) 1

def weylOperator (short : Bool) : Points k :=
  if short then simpleNormalizer k 0 * simpleNormalizer k 2 * simpleNormalizer k 3
    else simpleNormalizer k 1

def rootConjugator (short : Bool) : Points k :=
  if short then rootPoint k (negativeSimpleRoot 0) 1 * rootPoint k (negativeSimpleRoot 2) 1 *
    rootPoint k (negativeSimpleRoot 3) 1 else rootPoint k (negativeSimpleRoot 1) 1

private def positiveAction (z : HyperbolicSpace k 4) : HyperbolicSpace k 4 :=
  (![z.1 0 + z.1 1,z.1 1,z.1 2 + z.1 3 + z.2 2 + z.2 3,z.1 3 + z.2 2],
    ![z.2 0,z.2 0 + z.2 1,z.2 2,z.2 2 + z.2 3])

private def negativeAction (z : HyperbolicSpace k 4) : HyperbolicSpace k 4 :=
  (![z.1 0,z.1 0 + z.1 1,z.1 2,z.1 2 + z.1 3],
    ![z.2 0 + z.2 1,z.2 1,z.1 2 + z.1 3 + z.2 2 + z.2 3,z.1 2 + z.2 3])

private theorem positive_apply (z : HyperbolicSpace k 4) :
    (naturalAction k (rootOperator k true)).1 z = positiveAction k z := by
  simp only [rootOperator,↓reduceIte,map_mul,naturalAction_rootPoint,
    Subgroup.coe_mul,LinearEquiv.mul_apply,rootAction_spec]
  dsimp [simpleRoot,typeDSimpleRootIndex]
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAction,positiveAction]
    norm_num [Pi.single_apply,CharTwo.neg_eq,sub_eq_add_neg,mul_add,add_mul,Fin.ext_iff] <;> ring

private theorem negative_apply (z : HyperbolicSpace k 4) :
    (naturalAction k (rootConjugator k true)).1 z = negativeAction k z := by
  simp only [rootConjugator,↓reduceIte,map_mul,naturalAction_rootPoint,
    Subgroup.coe_mul,LinearEquiv.mul_apply,rootAction_spec]
  dsimp [negativeSimpleRoot,simpleRoot,typeDSimpleRootIndex,negativeRoot]
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAction,negativeAction]
    norm_num [Pi.single_apply,CharTwo.neg_eq,sub_eq_add_neg,mul_add,add_mul,Fin.ext_iff] <;> ring

omit [IsAlgClosed k] in
private theorem negative_involutive (z : HyperbolicSpace k 4) :
    negativeAction k (negativeAction k z) = z := by
  have h2 : (2:k)=0 := CharP.cast_eq_zero k 2
  have h4 : (4:k)=0 := by linear_combination (2:k)*h2
  apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [negativeAction] <;> ring_nf <;> simp only [h2,h4,mul_zero,add_zero,zero_add]

theorem rootConjugator_inv (short : Bool) :
    (rootConjugator k short)⁻¹ = rootConjugator k short := by
  cases short
  · simp [rootConjugator]
  · apply inv_eq_of_mul_eq_one_left
    apply naturalAction_injective k
    rw [map_mul,map_one]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change (naturalAction k (rootConjugator k true)).1
      ((naturalAction k (rootConjugator k true)).1 z) = z
    rw [negative_apply,negative_apply,negative_involutive]

theorem rootOperator_conjugate (short : Bool) :
    rootConjugator k short * rootOperator k short * (rootConjugator k short)⁻¹ =
      weylOperator k short := by
  rw [rootConjugator_inv]
  cases short
  · simp only [rootConjugator,rootOperator,weylOperator,Bool.false_eq_true,↓reduceIte]
    apply naturalAction_injective k
    simp only [map_mul,naturalAction_rootPoint]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simp only [Subgroup.coe_mul,LinearEquiv.mul_apply,rootAction_spec,simpleNormalizer_apply]
    have h2 : (2:k)=0 := CharP.cast_eq_zero k 2
    have h3 : (3:k)=1 := by linear_combination h2
    dsimp [simpleRoot,negativeSimpleRoot,typeDSimpleRootIndex,negativeRoot]
    apply Prod.ext <;> funext p <;> fin_cases p
    all_goals
      dsimp [rootAction,simpleAction]
      norm_num [Pi.single_apply,CharTwo.neg_eq,sub_eq_add_neg,mul_add,add_mul,Fin.ext_iff]
      <;> ring_nf <;> simp [h2,h3]
  · apply naturalAction_injective k
    simp only [map_mul]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simp only [Subgroup.coe_mul,LinearEquiv.mul_apply,negative_apply,positive_apply]
    simp only [weylOperator,↓reduceIte,map_mul,Subgroup.coe_mul,LinearEquiv.mul_apply,
      simpleNormalizer_apply]
    have h2 : (2:k)=0 := CharP.cast_eq_zero k 2
    have h3 : (3:k)=1 := by linear_combination h2
    have h4 : (4:k)=0 := by linear_combination (2:k)*h2
    have h6 : (6:k)=0 := by linear_combination (3:k)*h2
    have h9 : (9:k)=1 := by linear_combination (4:k)*h2
    apply Prod.ext <;> funext p <;> fin_cases p
    all_goals
      dsimp [negativeAction,positiveAction,simpleAction]
      ring_nf
      simp only [h2,h3,h4,h6,h9,mul_zero,mul_one,add_zero,zero_add]

end
end Triality.RestrictedWeights.BasicDisplacement
