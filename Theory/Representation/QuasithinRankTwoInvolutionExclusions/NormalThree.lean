module
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer

/-!
# Normal cubic subgroups and rank-two moved planes above dimension four

An involution inverting a fixed-point-free cubic operator has displacement
rank half the ambient dimension. Thus a rank-two involution in dimension
greater than four centralizes the cubic operator, which is transitive on
the three nonzero vectors of its moved plane. Faithful irreducibility
supplies fixed-point-freeness for any normal subgroup of order three.

This extends the dimension-six calculation to the central three-covers in
Aschbacher--Smith G.11.7 and the strict nontransitivity of 6.2.16(6).
-/

public noncomputable section
namespace Representation.RankTwo
open Subgroup Module
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Inversion of a fixed-point-free cubic is impossible for rank two above degree four. -/
theorem commute_of_rank_two_normal_three_of_degree_gt_four
    (ρ : Representation (ZMod 2) G V) (a c : G)
    (hd : 4 < finrank (ZMod 2) V) (ha : a*a=1) (hc : orderOf c=3)
    (hn : (zpowers c).Normal) (hfix : ∀ w, ρ c w=w → w=0)
    (hr : finrank (ZMod 2) (movedSpace ρ a)=2) : Commute c a := by
  rcases commute_or_invert_of_normal_three c a hc hn with h | h
  · exact h
  · have ht : (ρ c)^3=1 := by rw [←map_pow,←hc,pow_orderOf_eq_one,map_one]
    have hb : ρ a * ρ a=1 := by rw [←map_mul,ha,map_one]
    have hbt : ρ a * ρ c=(ρ c)^2 * ρ a := by rw [←map_pow,←map_mul,←map_mul,h]
    have hf := finrank_range_inverting_cubic (ρ c) (ρ a) ht hfix hb hbt
    change 2 * finrank (ZMod 2) (movedSpace ρ a) = _ at hf
    omega

/-- A fixed-point-free normal cubic acts transitively on the original moved plane. -/
theorem stabilizerTransitive_of_rank_two_normal_three_of_degree_gt_four
    (ρ : Representation (ZMod 2) G V) (a c : G)
    (hd : 4 < finrank (ZMod 2) V) (ha : a*a=1) (hc : orderOf c=3)
    (hn : (zpowers c).Normal) (hfix : ∀ w, ρ c w=w → w=0)
    (hr : finrank (ZMod 2) (movedSpace ρ a)=2) :
    StabilizerTransitive ρ (movedSpace ρ a) := by
  apply stabilizerTransitive_of_order_three ρ a c hr
    (commute_of_rank_two_normal_three_of_degree_gt_four ρ a c hd ha hc hn hfix hr)
  · rw [←hc,pow_orderOf_eq_one]
  · intro w _ hw
    exact hfix w hw

/-- The actual normal subgroup of order three supplies its cubic generator and
fixed-point-freeness in any faithful irreducible binary action. -/
theorem stabilizerTransitive_of_irreducible_normal_subgroup_three
    [Finite G] (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (C : Subgroup G) [C.Normal] (hC : Nat.card C=3)
    (a : G) (hd : 4 < finrank (ZMod 2) V) (ha : a*a=1)
    (hr : finrank (ZMod 2) (movedSpace ρ a)=2) :
    StabilizerTransitive ρ (movedSpace ρ a) := by
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC])
  have hcG : orderOf (c : G)=3 := (orderOf_coe c).trans hc
  have he : zpowers (c : G)=C := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    rw [Nat.card_zpowers,hcG,hC]
  have hn : (zpowers (c : G)).Normal := by rw [he]; infer_instance
  exact stabilizerTransitive_of_rank_two_normal_three_of_degree_gt_four ρ a c hd ha hcG hn
    (fixed_free_of_faithful_irreducible_normal_three ρ hf c hcG hn) hr
end Representation.RankTwo
