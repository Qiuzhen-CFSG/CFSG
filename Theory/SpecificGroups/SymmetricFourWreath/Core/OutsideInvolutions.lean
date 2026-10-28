module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.FixedCounts

/-!
# Centralizers of involutions outside the marked quotient core

An involution of P/Z outside Q/Z has a centralizer of order sixteen which
is not abelian. The proof counts its thirty-two lifts and supplies one of
four explicit pairs whose images do not commute. This prevents an elementary
subgroup of order sixteen from containing that involution.

Source: Aschbacher–Smith 13.9.6, printed p.971 (PDF p.988).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private def coreCondition (x : P) : Prop :=
  x.left 1*(x.left turn)⁻¹=1 ∨ x.left 1*(x.left turn)⁻¹=DihedralGroup.r 2
private instance (x : P) : Decidable (coreCondition x) := inferInstanceAs (Decidable (_∨_))
private def commutationCondition (x y : P) : Prop :=
  y*x=x*y ∨ y*x=centralInP*(x*y)
private instance (x y : P) : Decidable (commutationCondition x y) := inferInstanceAs (Decidable (_∨_))

private theorem centralizerCount : ∀x : P, ¬coreCondition x →
    (x*x=1 ∨ x*x=centralInP) → Fintype.card {y : P // commutationCondition x y}=32 := by
  decide +kernel

theorem card_centralFiber_of_involution (x : P) (hx : x∉coreInP)
    (hs : centralProjection x * centralProjection x=1) : Nat.card (centralFiber x)=32 := by
  have hsq : x*x=1 ∨ x*x=centralInP := by
    apply (mem_centralLine _).mp
    apply (QuotientGroup.eq_one_iff _).mp
    change centralProjection (x*x)=1
    rw [map_mul]
    exact hs
  let e : centralFiber x ≃ {y : P // commutationCondition x y} :=
    Equiv.subtypeEquivRight (mem_centralFiber x)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  exact centralizerCount x (fun h=>hx ((mem_coreInP x).mpr h)) hsq

private def witnessFirst : Fin 4 → P := ![
  pair (DihedralGroup.r 1,1), pair (1,DihedralGroup.r 1),
  pair (1,DihedralGroup.sr 1), pair (1,DihedralGroup.sr 0)]
private def witnessSecond : Fin 4 → P := ![
  pair (DihedralGroup.sr 0,1), pair (1,DihedralGroup.sr 0),
  pair (DihedralGroup.r 1,DihedralGroup.r 1),pair (DihedralGroup.r 1,DihedralGroup.r 1)]

private theorem witnessCheck : ∀x : P, ¬coreCondition x → (x*x=1 ∨ x*x=centralInP) →
    ∃i : Fin 4, commutationCondition x (witnessFirst i) ∧
      commutationCondition x (witnessSecond i) ∧
      ¬commutationCondition (witnessFirst i) (witnessSecond i) := by
  decide +kernel

theorem centralFiber_noncommuting (x : P) (hx : x∉coreInP)
    (hs : centralProjection x * centralProjection x=1) :
    ∃a∈centralFiber x, ∃b∈centralFiber x,
      ¬Commute (centralProjection a) (centralProjection b) := by
  have hsq : x*x=1 ∨ x*x=centralInP := by
    apply (mem_centralLine _).mp
    apply (QuotientGroup.eq_one_iff _).mp
    change centralProjection (x*x)=1
    rw [map_mul]
    exact hs
  obtain ⟨i,ha,hb,hn⟩ := witnessCheck x (fun h=>hx ((mem_coreInP x).mpr h)) hsq
  refine ⟨witnessFirst i,(mem_centralFiber x _).mpr ha,
    witnessSecond i,(mem_centralFiber x _).mpr hb,?_⟩
  intro hc
  exact hn ((centralProjection_commute _ _).mp hc.symm)
end SymmetricFourWreath
