module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Quotient

/-!
# Fixed points in the literal central quotient

Every Sylow element outside Q centralizes exactly eight lifts in Q modulo
its diagonal central involution. Consequently its fixed subgroup in Q/Z
has order four. The finite certificate uses the two dihedral coordinates;
the public statement concerns the actual quotient centralizer preimage.

Source: the no-transvection calculation in Aschbacher–Smith 13.9.8,
printed p.972 (PDF p.989).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidablePred (·∈coreInP) := fun x=>decidable_of_iff
  (x.left 1*(x.left turn)⁻¹=1 ∨ x.left 1*(x.left turn)⁻¹=DihedralGroup.r 2)
  (mem_coreInP x).symm

def centralFiber (x : P) : Subgroup P :=
  (centralizer ({centralProjection x} : Set CentralQuotient)).comap centralProjection

theorem mem_centralFiber (x y : P) : y∈centralFiber x ↔
    y*x=x*y ∨ y*x=centralInP*(x*y) := by
  change centralProjection y∈centralizer ({centralProjection x} : Set CentralQuotient) ↔ _
  rw [mem_centralizer_singleton_iff]
  exact centralProjection_commute y x

private instance (x : P) : DecidablePred (·∈centralFiber x) := fun y=>decidable_of_iff
  (y*x=x*y ∨ y*x=centralInP*(x*y)) (mem_centralFiber x y).symm
private instance (x : P) : DecidablePred (·∈(coreInP⊓centralFiber x : Subgroup P)) := fun y=>
  inferInstanceAs (Decidable (y∈coreInP ∧ y∈centralFiber x))

private def coreCondition (x : P) : Prop :=
  x.left 1*(x.left turn)⁻¹=1 ∨ x.left 1*(x.left turn)⁻¹=DihedralGroup.r 2
private instance (x : P) : Decidable (coreCondition x) := inferInstanceAs (Decidable (_∨_))
private def commutationCondition (x y : P) : Prop :=
  y*x=x*y ∨ y*x=centralInP*(x*y)
private instance (x y : P) : Decidable (commutationCondition x y) := inferInstanceAs (Decidable (_∨_))

private theorem fixedCount : ∀x : P, ¬coreCondition x →
    Fintype.card {y : P // coreCondition y ∧ commutationCondition x y}=8 := by
  decide +kernel

theorem card_core_fixed (x : P) (hx : x∉coreInP) :
    Nat.card (coreInP⊓centralFiber x : Subgroup P)=8 := by
  let e : (coreInP⊓centralFiber x : Subgroup P) ≃
      {y : P // coreCondition y ∧ commutationCondition x y} :=
    Equiv.subtypeEquivRight (fun y=>(mem_coreInP y).and (mem_centralFiber x y))
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  exact fixedCount x (fun h=>hx ((mem_coreInP x).mpr h))
end SymmetricFourWreath
