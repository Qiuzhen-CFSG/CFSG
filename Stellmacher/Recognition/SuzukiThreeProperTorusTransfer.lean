module

public import Stellmacher.Recognition.SuzukiThreeCentralizingFusion
public import Theory.GroupAction.FourFixedCyclicStabilizer
public import Theory.GroupAction.CentralizerFixedPairs
import Mathlib.Tactic.Linarith

/-!
# The order-eight obstruction for a centralizing Suzuki swap

At q = 3 the transfer conclusion can be replaced by a direct obstruction.
The centralizer of a torus involution acts on its four fixed points, and the
kernel lies in the cyclic two-point stabilizer. Every element of order eight
in that centralizer therefore has fourth power equal to the involution.
Conjugacy of involutions transports this property to the point swap. A torus
generator would then have fourth power equal to the swap, although the former
fixes the base point and the latter moves it.

The fixed-point census follows from torus fusion: the involution centralizer
is transitive on ordered pairs of distinct fixed points, whose stabilizer has
order eight. Its order 96 therefore gives `96 = 8 f (f - 1)`, so `f = 4`.
This gives a direct alternative to Suzuki (1965), Section II, Lemma 6.
No central-cover classification or quaternion-Sylow theorem is used.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- The fourth power of a torus generator has four fixed points. The
centralizer order and rigidity of torus fusion suffice for this census. -/
public theorem torus_fourth_power_fixed_card
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (k : stabilizer (stabilizer G a) b) (hk : orderOf k = 8) :
    Nat.card {x : Ω // ((k : stabilizer G a) : G) ^ 4 • x = x} = 4 := by
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [h.degree]; decide)
  let : Finite (stabilizer (stabilizer G a) b) :=
    Nat.finite_of_card_ne_zero (by rw [h.twoPoint_card b hb]; decide)
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  let jK := k ^ 4
  let j : G := ((jK : stabilizer G a) : G)
  have hj : orderOf j = 2 := by
    simp only [j, jK, Subgroup.orderOf_coe]
    rw [orderOf_pow, hk]
    decide
  have htb : t • b = a := by
    rw [← hta, ← mul_smul, ← pow_two, ht2, one_smul]
  have hcount := MulAction.card_centralizer_eq_twoPoint_mul_fixed_pairs
    h.doubly_transitive a b hb.symm j
    (mem_stabilizer_iff.mp jK.val.property) (mem_stabilizer_iff.mp jK.property)
    (fun l => congrArg (fun z : stabilizer (stabilizer G a) b =>
      ((z : stabilizer G a) : G)) (mul_comm' jK l))
    (fun l hl => congrArg (fun z : stabilizer (stabilizer G a) b =>
      ((z : stabilizer G a) : G))
      (h.twoPoint_eq_of_isConj_of_swap_centralizes b hb t hta htb htK jK l hl).symm)
  rw [hc j hj, h.twoPoint_card b hb] at hcount
  change Nat.card {x : Ω // j • x = x} = 4
  have hpos : 0 < Nat.card {x : Ω // j • x = x} := by
    by_contra hn
    have hz : Nat.card {x : Ω // j • x = x} = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.mul_zero] at hcount
    contradiction
  have hsub := Nat.sub_add_cancel hpos
  nlinarith

/-- Four fixed points for the torus involution exclude a centralizing swap.
The fixed-point census is the only local input beyond involution conjugacy. -/
public theorem false_of_centralizing_swap_of_four_fixed
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (hfour : ∀ k : stabilizer (stabilizer G a) b, orderOf k = 8 →
      Nat.card {x : Ω // ((k : stabilizer G a) : G) ^ 4 • x = x} = 4) :
    False := by
  let : Finite G := h.finite_group
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := stabilizer (stabilizer G a) b)
  rw [h.twoPoint_card b hb] at hk
  let x : G := ((k : stabilizer G a) : G)
  let j : G := x ^ 4
  have hx : orderOf x = 8 := by
    simpa only [x, Subgroup.orderOf_coe] using hk
  have hj : orderOf j = 2 := by rw [orderOf_pow, hx]; decide
  have hja : j • a = a := by
    have hh := mem_stabilizer_iff.mp (k ^ 4).val.property
    change (((k ^ 4 : stabilizer (stabilizer G a) b) : stabilizer G a) : G) • a = a at hh
    simpa only [Subgroup.coe_pow] using hh
  have hjb : j • b = b := by
    change (((k ^ 4 : stabilizer (stabilizer G a) b) : stabilizer G a) : G) • b = b
    exact mem_stabilizer_iff.mp (k ^ 4).property
  obtain ⟨f, hfcyc, hjker⟩ :=
    MulAction.exists_perm_four_cyclic_kernel_of_fixed_card_four a b j hja hjb (hfour k hk)
  let : IsCyclic f.ker := hfcyc
  have htne : t ≠ 1 := by
    intro he
    exact hb (by simpa only [he, one_smul] using hta.symm)
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 htne
  have hxt : Commute x t := by
    change x * t = t * x
    have he := congrArg (fun z : G => t * z) (htK k)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he
  have heq : x ^ 4 = t :=
    Subgroup.pow_four_eq_of_involution_centralizer_perm_four j hj f hjker
      (fun i hi => hconj i j hi hj) t x htord hx hxt
  exact hb (hta.symm.trans (by rw [← heq]; exact hja))

/-- The involution census rules out a centralizing point swap. -/
public theorem false_of_centralizing_swap_of_involution_census
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j) :
    False := by
  exact h.false_of_centralizing_swap_of_four_fixed b hb t ht2 hta htK hconj
    (h.torus_fourth_power_fixed_card b hb t ht2 hta htK hc)

/-! The transfer-shaped wrapper is kept separate so consumers can supply the
fixed-point census proved by their involution-counting module. -/
public theorem exists_normal_index_four_of_proper_torus_fixed_census
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (_hbranch : ¬ ∃ u : Q, u ≠ 1 ∧
      ∀ k : stabilizer (stabilizer G a) b,
        Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G))
    (hfour : ∀ k : stabilizer (stabilizer G a) b, orderOf k = 8 →
      Nat.card {x : Ω // ((k : stabilizer G a) : G) ^ 4 • x = x} = 4) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  exact (h.false_of_centralizing_swap_of_four_fixed b hb t ht2 hta htK hconj hfour).elim

/-- The proper-torus transfer conclusion from the involution census, with
the four-fixed-point input discharged. -/
public theorem properTorus_transfer_index_four
    [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht2 : t ^ 2 = 1)
    (hta : t • a = b) (_htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 →
      Nat.card (Subgroup.centralizer ({j} : Set G)) = 96)
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (hbranch : ¬ ∃ u : Q, u ≠ 1 ∧
      ∀ k : stabilizer (stabilizer G a) b,
        Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  exact h.exists_normal_index_four_of_proper_torus_fixed_census b hb t ht2 hta htK
    hconj hbranch (h.torus_fourth_power_fixed_card b hb t ht2 hta htK hc)

end Stellmacher.Recognition.SuzukiThreeHypotheses
