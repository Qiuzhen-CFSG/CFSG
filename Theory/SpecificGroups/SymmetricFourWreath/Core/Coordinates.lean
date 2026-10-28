module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The extraspecial subgroup in the dihedral wreath wreathElements

Two explicit commuting quaternion embeddings give the source subgroup Q of
order 32. Its elements are exactly the wreath elements whose two dihedral
wreathElements agree modulo the dihedral center. All finite checks are on the
literal order-128 Sylow, with quaternion words supplying the witnesses.

Source: Aschbacher–Smith 13.9.6, printed p.971 (PDF p.988).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
def wreathElement (a b : D8) (q : C2) : P := ⟨fun i=>if i=1 then a else b,q⟩
def quaternionI (side : Bool) : P :=
  if side then wreathElement (DihedralGroup.r 0) (DihedralGroup.r 2) turn
  else wreathElement (DihedralGroup.r 1) (DihedralGroup.r 1) 1
def quaternionJ (side : Bool) : P :=
  if side then wreathElement (DihedralGroup.r 1) (DihedralGroup.r 1) turn
  else wreathElement (DihedralGroup.sr 0) (DihedralGroup.sr 2) turn
def quaternionFunction (side : Bool) : QuaternionGroup 2 → P
  | .a i => quaternionI side ^ i.val
  | .xa i => quaternionJ side * quaternionI side ^ i.val

def quaternionEmbedding (side : Bool) : QuaternionGroup 2 →* P where
  toFun := quaternionFunction side
  map_one' := by cases side <;> decide +kernel
  map_mul' := by cases side <;> decide +kernel

theorem quaternionEmbedding_injective (side : Bool) :
    Function.Injective (quaternionEmbedding side) := by cases side <;> decide +kernel

theorem quaternionEmbedding_commute (a b : QuaternionGroup 2) :
    Commute (quaternionEmbedding false a) (quaternionEmbedding true b) := by
  change quaternionEmbedding false a * quaternionEmbedding true b = _
  revert a b
  decide +kernel

def quaternionProduct : QuaternionGroup 2 × QuaternionGroup 2 →* P where
  toFun x := quaternionEmbedding false x.1 * quaternionEmbedding true x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul]
    calc
      _ = quaternionEmbedding false x.1 *
          (quaternionEmbedding false y.1 * quaternionEmbedding true x.2) *
            quaternionEmbedding true y.2 := by simp only [mul_assoc]
      _ = quaternionEmbedding false x.1 *
          (quaternionEmbedding true x.2 * quaternionEmbedding false y.1) *
            quaternionEmbedding true y.2 := by rw [(quaternionEmbedding_commute y.1 x.2).eq]
      _ = _ := by simp only [mul_assoc]


def coreInP : Subgroup P := quaternionProduct.range

private instance coreInP_decidable : DecidablePred (·∈coreInP) := fun x=>
  inferInstanceAs (Decidable (∃y,quaternionProduct y=x))

theorem mem_coreInP (x : P) : x∈coreInP ↔
    x.left 1 * (x.left turn)⁻¹ = 1 ∨
      x.left 1 * (x.left turn)⁻¹ = DihedralGroup.r 2 := by
  revert x
  decide +kernel

theorem card_coreInP : Nat.card coreInP = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end SymmetricFourWreath
