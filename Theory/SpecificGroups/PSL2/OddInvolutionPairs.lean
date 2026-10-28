module

public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.GroupTheory.InvolutionOddPairCount
public import Theory.GroupTheory.ConjugacyOrderCensus
public import BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.Tactic.Linarith

/-!
# Counting odd-product involution pairs in characteristic-two PSL₂

The genuine root subgroup is the full centralizer of each of its nonidentity
elements, has exponent two and has order q. Conjugacy of all involutions and
the matrix group order q(q²−1) therefore give q²−1 involutions. For each first
factor, the only forbidden second factors are the q−2 other nonidentity
elements of its root centralizer. In particular, the equal-factor pair has
identity product of odd order one and is retained.

We use the actual projective special linear matrix quotient throughout.
Source: GLS, Volume 4, Chapter 2, Lemma 12.8(a), using the rank-one facts of
Chapter 4, Lemma 3.2(a), and Huppert II.6.14 for the group order.
-/

noncomputable section
namespace Theory.PSL2
open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
private theorem root_square {x : PSL2MatrixGroup K} (hx : x ∈ PUnip K) : x ^ 2 = 1 := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := (mem_Unip_iff g).mp hg
  rw [← map_pow, pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero, map_one]

private theorem centralizer_root_equiv (a : PSL2MatrixGroup K) (ha : orderOf a = 2) :
    ∃ _e : centralizer ({a} : Set (PSL2MatrixGroup K)) ≃ PUnip K,
      ∀ x : centralizer ({a} : Set (PSL2MatrixGroup K)), ((x : PSL2MatrixGroup K) ^ 2 = 1) := by
  obtain ⟨g, t, ht, hg, _, _⟩ := involution_root_geometry a ha
  let f := MulAut.conj g
  have hmem (x : PSL2MatrixGroup K) : x ∈ centralizer ({a} : Set (PSL2MatrixGroup K)) ↔ f x ∈ PUnip K := by
    rw [← centralizer_root_eq ht, ← hg]
    simp only [mem_centralizer_singleton_iff, ← map_mul, f, (MulAut.conj g).injective.eq_iff]
  refine ⟨Equiv.subtypeEquiv f.toEquiv hmem, ?_⟩
  intro x
  apply f.injective
  rw [map_pow, map_one]
  exact root_square ((hmem x).mp x.property)

private theorem involution_centralizer_card (a : PSL2MatrixGroup K) (ha : orderOf a = 2) :
    Nat.card (centralizer ({a} : Set (PSL2MatrixGroup K))) = Nat.card K := by
  obtain ⟨e, _⟩ := centralizer_root_equiv a ha
  exact (Nat.card_congr e).trans PUnip_card

private theorem involution_centralizer_square
    (a : PSL2MatrixGroup K) (ha : orderOf a = 2) (b : PSL2MatrixGroup K) (hc : Commute a b) :
    b ^ 2 = 1 := by
  obtain ⟨_, he⟩ := centralizer_root_equiv a ha
  exact he ⟨b, mem_centralizer_singleton_iff.mpr hc.symm.eq⟩

/-- There are q²−1 involutions in the genuine characteristic-two PSL₂. -/
public theorem card_involutions_char_two :
    Nat.card {a : PSL2MatrixGroup K // orderOf a = 2} = Nat.card K ^ 2 - 1 := by
  let a : PSL2MatrixGroup K := PWeyl K
  have ha : orderOf a = 2 := orderOf_eq_prime PWeyl_isInvolution.sq_eq_one PWeyl_isInvolution.ne_one
  have hconj (b : PSL2MatrixGroup K) : orderOf b = 2 ↔ IsConj a b := by
    constructor
    · exact involutions_isConj a b ha
    · intro hb
      obtain ⟨g, rfl⟩ := isConj_iff.mp hb
      exact ((MulAut.conj g).orderOf_eq a).trans ha
  have he := Nat.card_congr (Equiv.subtypeEquivRight hconj)
  have hc := ConjClasses.nat_card_carrier_mul_card_centralizer a
  change Nat.card {b : PSL2MatrixGroup K // IsConj a b} * Nat.card (centralizer ({a} : Set (PSL2MatrixGroup K))) = Nat.card (PSL2MatrixGroup K) at hc
  rw [← he, involution_centralizer_card a ha] at hc
  have hgroup := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
  simp only [center_SL2_eq_bot, Nat.card_eq_fintype_card, Fintype.card_unique, mul_one] at hgroup
  have hc' : Nat.card {a : PSL2MatrixGroup K // orderOf a = 2} * Nat.card K =
      Nat.card K * (Nat.card K ^ 2 - 1) := hc.trans hgroup
  rw [mul_comm] at hc'
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) hc'

private theorem count_arithmetic {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 - 1 = (q - 1) * (q + 1) ∧
      (q ^ 2 - 1) - (q - 2) = q * (q - 1) + 1 := by
  have h1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have h2 : q - 2 + 2 = q := Nat.sub_add_cancel hq
  have hsq : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hm : q * (q - 1) + q = q ^ 2 := by nlinarith
  constructor
  · nlinarith
  · omega

/-- For each first involution, q(q−1)+1 second involutions have odd-order
product. The equal-factor pair is included. -/
public theorem card_odd_second_factors_char_two (a : PSL2MatrixGroup K) (ha : orderOf a = 2) :
    Nat.card {b : {b : PSL2MatrixGroup K // orderOf b = 2} // Odd (orderOf (a * b.val))} =
      Nat.card K * (Nat.card K - 1) + 1 := by
  rw [Theory.GroupTheory.InvolutionOddPairCount.card_second_factors involution_centralizer_square a ha,
    card_involutions_char_two, involution_centralizer_card a ha]
  exact (count_arithmetic (Finite.one_lt_card (α := K))).2

/-- The ordered odd-product involution-pair count in the actual matrix quotient. -/
public theorem card_odd_involution_pairs_char_two :
    Nat.card {p : PSL2MatrixGroup K × PSL2MatrixGroup K //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} =
      (Nat.card K - 1) * (Nat.card K + 1) * (Nat.card K * (Nat.card K - 1) + 1) := by
  rw [Theory.GroupTheory.InvolutionOddPairCount.card_pairs involution_centralizer_square involution_centralizer_card,
    card_involutions_char_two]
  obtain ⟨h1, h2⟩ := count_arithmetic (Finite.one_lt_card (α := K))
  rw [h2, h1]

end Theory.PSL2
