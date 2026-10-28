module

public import Stellmacher.Recognition.SuzukiThreeTorus
public import Theory.GroupTheory.PGroup.OrderTwentySevenEightAut

/-!
# Exponent of Suzuki's root group at q = 3

The cyclic two-point stabilizer acts faithfully by conjugation on the root
group of order 27. A generator gives an automorphism of order eight. The
fifth-power swapping involution centralizes the fourth power of that generator,
so the existing centralizer census gives precisely three fixed root elements.
The order-27 automorphism lemma then proves exponent three, without assuming
that the root group is noncommutative.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section II Lemmas 7–8 and Section III Lemma 11.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses
open MulAction
variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- A torus generator acts faithfully with order eight, and its fourth power
fixes exactly three root elements. -/
public theorem exists_root_aut_eight_fixed_three (b : Ω) (hb : b ≠ a) :
    ∃ f : MulAut Q, orderOf f = 8 ∧ Nat.card {q : Q // (f ^ 4) q = q} = 3 := by
  let : Finite G := h.finite_group
  let K := stabilizer (stabilizer G a) b
  let : IsCyclic K := h.twoPoint_cyclic b hb
  let ρ : K →* MulAut Q := (MulAut.conjNormal (H := Q)).comp K.subtype
  have hinj : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply eq_bot_iff.mpr
    intro k hk
    apply h.twoPoint_eq_one_of_centralizes_root b hb k
    intro q
    have he := congrArg (fun f : MulAut Q => ((f q : stabilizer G a) : G)) hk
    change ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
      ((k : stabilizer G a) : G)⁻¹ = ((q : stabilizer G a) : G) at he
    calc
      _ = (((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
        ((k : stabilizer G a) : G)⁻¹) * ((k : stabilizer G a) : G) := by group
      _ = _ := by rw [he]
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hk8 : orderOf k = 8 := hk.trans (h.twoPoint_card b hb)
  have hf : orderOf (ρ k) = 8 := (orderOf_injective ρ hinj k).trans hk8
  obtain ⟨t, _, hta, htb, htK⟩ := h.exists_swap_pow_five b hb
  let j : K := k ^ 4
  have hj : orderOf (j : G) = 2 := by
    simp only [j, Subgroup.orderOf_coe, orderOf_pow, hk8]
    decide
  have hj2 : (j : G) ^ 2 = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
  have hj5 : (j : G) ^ 5 = (j : G) := by
    calc
      _ = ((j : G) ^ 2) ^ 2 * (j : G) := by group
      _ = _ := by rw [hj2]; simp
  have hjt : Commute (j : G) t := by
    have he := htK j
    rw [hj5] at he
    change (j : G) * t = t * (j : G)
    calc
      _ = t * (t⁻¹ * (j : G) * t) := by group
      _ = _ := by rw [he]
  have hc := h.rootCentralizer_involution_card b hb t hta htb j hj hjt
  refine ⟨ρ k, hf, ?_⟩
  have heq (q : Q) : (ρ k ^ 4) q = q ↔ q ∈ rootCentralizer (Q := Q) b j := by
    rw [← map_pow]
    change ρ j q = q ↔ _
    rw [mem_rootCentralizer]
    constructor
    · intro he
      have he' := congrArg (fun q : Q => ((q : stabilizer G a) : G)) he
      change (j : G) * ((q : stabilizer G a) : G) * (j : G)⁻¹ =
        ((q : stabilizer G a) : G) at he'
      change (j : G) * ((q : stabilizer G a) : G) =
        ((q : stabilizer G a) : G) * (j : G)
      calc
        _ = ((j : G) * ((q : stabilizer G a) : G) * (j : G)⁻¹) * (j : G) := by group
        _ = _ := by rw [he']
    · intro he
      apply Subtype.ext
      apply Subtype.ext
      change (j : G) * ((q : stabilizer G a) : G) * (j : G)⁻¹ =
        ((q : stabilizer G a) : G)
      rw [he.eq]
      group
  exact (Nat.card_congr (Equiv.subtypeEquivRight heq)).trans hc

/-- Every root element has cube one, from Suzuki's original action hypotheses. -/
public theorem root_cube (b : Ω) (hb : b ≠ a) : ∀ q : Q, q ^ 3 = 1 := by
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.root_card]; decide)
  obtain ⟨f, hf, hfixed⟩ := h.exists_root_aut_eight_fixed_three b hb
  exact OrderTwentySeven.cube_eq_one_of_eight_aut h.root_card f hf hfixed

end Stellmacher.Recognition.SuzukiThreeHypotheses
