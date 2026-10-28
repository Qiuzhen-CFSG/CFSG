module
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction

/-!
# Orders of groups with a self-centralizing minus extraspecial core

Conjugation on the five singular central cosets has kernel exactly the
normal core. Its image lies in S₅, so the full group has order dividing
32 · 120. This controls overgroups of the order-1920 J₂ local group while
retaining the possible outer extension.

Source: DGS, Groups and Graphs (1985), (5.14)--(5.16), pp.116--117,
and the restoration of the field-four case of (10.9), p.163.
-/

public section
open Subgroup
namespace MinusExtraspecial
open AlternatingAction FixedFourCalculation.Outside

theorem card_dvd_of_self_centralizing_core {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [Q.Normal]
    (e : Q ≃* Model) (hc : centralizer (Q : Set H) ≤ Q) :
    Nat.card H ∣ 3840 := by
  let f := fivePointAction.comp (coreAction Q e)
  have hk : f.ker = Q := pointAction_kernel Q e hc
  have hi : Q.index ∣ 120 := by
    rw [←hk,index_ker]
    convert f.range.card_subgroup_dvd_card using 1
    ·
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hQ : Nat.card Q = 32 := (Nat.card_congr e.toEquiv).trans card_model
  rw [←Q.card_mul_index,hQ]
  exact Nat.mul_dvd_mul_left 32 hi


end MinusExtraspecial
