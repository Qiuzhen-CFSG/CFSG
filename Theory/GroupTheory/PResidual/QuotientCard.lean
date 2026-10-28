module

public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Quotient residual orders from embedded residuals

The order of the residual of K/N is the relative index of N in the
embedded residual of K. Thus two actual subgroups with the same embedded
residual have the same residual order modulo a common denominator.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem card_quotient_pResidual_eq_relIndex (p : ℕ) (K N : Subgroup G)
    [(N.subgroupOf K).Normal] :
    Nat.card (pResidual p (K ⧸ N.subgroupOf K)) =
      N.relIndex ((pResidual p K).map K.subtype) := by
  calc
    _ = (N.subgroupOf K).relIndex (pResidual p K) :=
      (Nat.card_congr (pResidualQuotientEquiv p (N.subgroupOf K)).toEquiv).symm
    _ = _ := relIndex_comap N K.subtype (pResidual p K)

theorem card_quotient_pResidual_eq_of_embedded_eq (p : ℕ) (K H N : Subgroup G)
    [(N.subgroupOf K).Normal] [(N.subgroupOf H).Normal]
    (he : (pResidual p K).map K.subtype = (pResidual p H).map H.subtype) :
    Nat.card (pResidual p (K ⧸ N.subgroupOf K)) =
      Nat.card (pResidual p (H ⧸ N.subgroupOf H)) := by
  rw [card_quotient_pResidual_eq_relIndex, card_quotient_pResidual_eq_relIndex, he]

end Subgroup
