module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecial
public import Theory.Frattini.BinarySquares

/-!
# The order-thirty-two rank-two extraspecial group

The rank-two extraspecial classification at order thirty-two leaves precisely
an internal central product of quaternion and dihedral groups of order eight.
Its Frattini subgroup is its center, so its Frattini quotient has order sixteen.
These facts prepare the faithful outer action used in the large-core case.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389;
the model reduction is proved in `RankTwoExtraspecial`.
-/

open Subgroup

namespace IsExtraspecial

/-- At order thirty-two, the rank-two model is the quaternion-dihedral
central product, with the actual embedded factors retained. -/
public theorem dihedral_quaternion_factors_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hP : Nat.card P = 32) :
    ∃ U V : Subgroup P, Nonempty (U ≃* QuaternionGroup 2) ∧
      Nonempty (V ≃* DihedralGroup 4) ∧ V ≤ centralizer (U : Set P) ∧
      U ⊔ V = ⊤ ∧ Nat.card (U ⊓ V : Subgroup P) = 2 := by
  rcases rank_two_classification hrank with h | h | h
  · obtain ⟨e⟩ := h
    have hc := Nat.card_congr e.toEquiv
    rw [hP, DihedralGroup.nat_card] at hc
    norm_num at hc
  · obtain ⟨e⟩ := h
    have hc := Nat.card_congr e.toEquiv
    rw [hP, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
    norm_num at hc
  · exact h

/-- The Frattini subgroup of an extraspecial two-group is its center. -/
public theorem frattini_eq_center_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P] :
    frattini P = center P := by
  have hP : IsPGroup 2 P := isPGroup 2 P
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hle : frattini P ≤ center P := by
    rw [hP.frattini_eq_closure_squares]
    exact (closure_le _).mpr (by rintro _ ⟨x, rfl⟩; exact square_mem_center x)
  have hne : frattini P ≠ ⊥ := by
    intro hbot
    let : IsElementaryAbelian 2 P :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hbot
    let : Nontrivial (P ⧸ center P) := quotient_nontrivial 2 P
    have hs : Subsingleton (P ⧸ center P) :=
      QuotientGroup.subsingleton_iff.mpr center_eq_top
    exact not_subsingleton (P ⧸ center P) hs
  have hd : Nat.card (frattini P) ∣ 2 := by
    rw [← center_order_p 2 P]
    exact card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
  · exact (hne (card_eq_one.mp hc)).elim
  · apply eq_of_le_of_card_ge hle
    rw [hc, center_order_p 2 P]

/-- The elementary space supporting the outer action has order sixteen. -/
public theorem card_frattini_quotient_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 32) : Nat.card (P ⧸ frattini P) = 16 := by
  have hc := card_eq_card_quotient_mul_card_subgroup (center P)
  rw [hP, center_order_p 2 P] at hc
  rw [frattini_eq_center_two]
  omega

end IsExtraspecial
