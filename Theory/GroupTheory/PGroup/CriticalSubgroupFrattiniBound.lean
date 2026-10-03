module

public import Theory.GroupTheory.PGroup.CentralQuotientQuadratic
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# A Frattini bound for critical subgroups with three central involutions

A critical subgroup contains the ambient center by its centralizer condition.
Consequently, when the ambient group has exactly three central involutions,
so does the critical subgroup. Its elementary central quotient admits an
anisotropic square-class map. The general quadratic Frattini bound, together
with the order-four first omega subgroup of its center, bounds its Frattini
quotient by sixteen. No transitivity assumption is needed.

Sources: Gorenstein, *Finite Groups*, Theorem 5.3.11, for critical subgroups;
the square-map argument for the three-involution problem in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- A critical subgroup of a finite two-group with exactly three central
involutions has Frattini quotient of order at most sixteen. -/
public theorem card_frattini_quotient_le_sixteen_of_three_central_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C) :
    Nat.card (C ⧸ frattini C) ≤ 16 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  have hmem (x : P) (hx : x ^ 2 = 1) : x ∈ C := by
    have hc : x ∈ centralizer (C : Set P) :=
      fun y _ => mem_center_iff.mp (hcentral x hx) y
    exact map_subtype_le (center C) (hC.centralizer_eq ▸ hc)
  have hcentralC (x : C) (hx : x ^ 2 = 1) : x ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp
      (hcentral x (congrArg Subtype.val hx)) y)
  let e : {x : P // orderOf x = 2} ≃ {x : C // orderOf x = 2} :=
    { toFun := fun x =>
        ⟨⟨x, hmem x (orderOf_eq_prime_iff.mp x.property).1⟩,
          (orderOf_injective C.subtype C.subtype_injective _).symm.trans x.property⟩
      invFun := fun x => ⟨(x.val : P), by simpa only [orderOf_coe] using x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hthreeC : Nat.card {x : C // orderOf x = 2} = 3 :=
    (Nat.card_congr e).symm.trans hthree
  have hfour := IsPGroup.card_omega_center_eq_four_of_three_central_involutions
    hcentralC hthreeC
  have hbound := (hP.to_subgroup C).card_frattini_quotient_le_sq_card_omega_center hcentralC
  simpa only [hfour, Nat.reducePow] using hbound

end IsCriticalPSubgroup
