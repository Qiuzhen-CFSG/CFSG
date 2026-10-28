module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Prime.Pow

/-!
# Product orders in the exceptional normalizer

The odd group A meets the normalizer of the four-group trivially: its
intersection centralizes the four-group, whose ambient centralizer is a
two-group. Thus the displayed product A(VX) has order 324 and X lies
outside A. The fixed-subgroup calculation then gives the literal plane
order nine.

Every subgroup D of order 27 in N_G(A) is normalized by A. Indeed AD is
a three-group with order dividing 324, so D has index one or three in AD.
This proves the normalization half of ExceptionalSylowControl without an
odd-centralizer-complement premise or a fixed-space calculation.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225. Fixed-space and relative-plane-normalizer calculations are
separate obligations.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
private theorem normalizer_centralizes_of_disjoint {A K : Subgroup G}
    (hn : K ≤ normalizer (A : Set G)) (hd : Disjoint A K) :
    A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G) := by
  intro a ha k hk
  have hAK : a * k * a⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((mem_normalizer_iff.mp ha.2 k).mp hk) (K.inv_mem hk)
  have hAA : a * k * a⁻¹ * k⁻¹ ∈ A := by
    have hh := A.mul_mem ha.1 ((mem_normalizer_iff.mp (hn hk) a⁻¹).mp (A.inv_mem ha.1))
    simpa only [mul_assoc] using hh
  have he : a * k * a⁻¹ * k⁻¹ = 1 := hd.le_bot ⟨hAA, hAK⟩
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

/-- The odd kernel has trivial intersection with the four-group normalizer. -/
public theorem exceptional_disjoint_four_normalizer (h : Janko1CentralizerData G)
    (A V : Subgroup G) (hA : Nat.card A = 27) (hV : Nat.card V = 4)
    (hVA : V ≤ normalizer (A : Set G)) : Disjoint A (normalizer (V : Set G)) := by
  have hAV : Disjoint A V := disjoint_of_coprime_natCard (by rw [hA, hV]; decide)
  have hc := normalizer_centralizes_of_disjoint hVA hAV
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  have hb := h.odd_inf_four_centralizer_eq_bot A V (by rw [hA]; decide) hV
  exact (le_inf inf_le_left hc).trans hb.le

/-- The literal complement VX is disjoint from A. -/
public theorem exceptional_complement_disjoint (h : Janko1CentralizerData G)
    (A V X : Subgroup G) (hA : Nat.card A = 27) (hV : Nat.card V = 4)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) : Disjoint A (V ⊔ X) := by
  apply (h.exceptional_disjoint_four_normalizer A V hA hV ?_).mono_right
    (sup_le V.le_normalizer hXV)
  rw [hN]
  exact le_sup_of_le_right le_sup_left

/-- The displayed exceptional normalizer has order 324. -/
public theorem exceptional_normalizer_card (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A) :
    Nat.card (normalizer (A : Set G)) = 324 := by
  obtain ⟨V, X, _, hV, hX, hXV, hN⟩ := e.normalizer_decomposition
  have hVX : Nat.card (V ⊔ X : Subgroup G) = 12 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint V X hXV
      (disjoint_of_coprime_natCard (by rw [hV, hX]; decide)), hV, hX]
  have hd := h.exceptional_complement_disjoint A V X e.card hV hXV hN
  have hn : V ⊔ X ≤ normalizer (A : Set G) := by rw [hN]; exact le_sup_right
  rw [hN, card_sup_eq_mul_of_normalizes_of_disjoint A (V ⊔ X) hn hd, e.card, hVX]

/-- The order-three complement is not contained in A. -/
public theorem exceptional_actor_outside (h : Janko1CentralizerData G)
    (A V X : Subgroup G) (hA : Nat.card A = 27) (hV : Nat.card V = 4)
    (hX : Nat.card X = 3) (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) : ¬ X ≤ A := by
  intro hXA
  have hd := (h.exceptional_complement_disjoint A V X hA hV hXV hN).mono_right
    (show X ≤ V ⊔ X from le_sup_right)
  have hb : X = ⊥ := eq_bot_iff.mpr (fun x hx => hd.le_bot ⟨hXA hx, hx⟩)
  simp [hb] at hX

/-- The fixed-subgroup order gives the order of the literal plane Y. -/
public theorem exceptional_plane_card_of_fixed_card (h : Janko1CentralizerData G)
    (A V X : Subgroup G) (hA : Nat.card A = 27) (hV : Nat.card V = 4)
    (hX : Nat.card X = 3) (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X))
    (hfixed : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3) :
    Nat.card (exceptionalPlane A X) = 9 := by
  have hd := (h.exceptional_complement_disjoint A V X hA hV hXV hN).mono
    (show A ⊓ centralizer (X : Set G) ≤ A from inf_le_left)
    (show X ≤ V ⊔ X from le_sup_right)
  have hc : X ≤ centralizer (A ⊓ centralizer (X : Set G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  rw [exceptionalPlane, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hc.trans (centralizer_le_normalizer _)) hd, hfixed, hX]

/-- Every subgroup of order 27 in N_G(A) is normalized by A. -/
public theorem exceptional_normalizes_order27 (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (D : Subgroup G) (hD : D ≤ normalizer (A : Set G)) (hDc : Nat.card D = 27) :
    A ≤ normalizer (D : Set G) := by
  let L := A ⊔ D
  have hLp : IsPGroup 3 L :=
    (IsPGroup.of_card (p := 3) (n := 3) (by simpa using e.card)).to_sup_of_normal_left'
      (IsPGroup.of_card (p := 3) (n := 3) (by simpa using hDc)) hD
  have hLdiv : Nat.card L ∣ 324 := by
    rw [← h.exceptional_normalizer_card A e]
    exact card_dvd_of_le (sup_le A.le_normalizer hD)
  have hLodd : Odd (Nat.card L) := by
    obtain ⟨n, hn⟩ := hLp.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hL81 : Nat.card L ∣ 81 := by
    have he : 324 = 4 * 81 := by decide
    rw [he] at hLdiv
    exact (hLodd.coprime_two_right.pow_right 2).dvd_of_dvd_mul_left hLdiv
  have hDL : D ≤ L := le_sup_right
  have hsubcard : Nat.card (D.subgroupOf L) = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv).trans hDc
  have hi := (D.subgroupOf L).index_mul_card
  rw [hsubcard] at hi
  have hidiv : (D.subgroupOf L).index ∣ 3 := by
    have hm : (D.subgroupOf L).index * 27 ∣ 3 * 27 := by
      simpa only [hi] using hL81
    exact Nat.dvd_of_mul_dvd_mul_right (by decide) hm
  have hnormal : (D.subgroupOf L).Normal := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hidiv with hone | hthree
    · exact normal_of_index_eq_one hone
    · apply normal_of_index_eq_minFac_card
      have hLc : Nat.card L = 81 := by omega
      rw [hLc, hthree]
      exact (Nat.prime_three.pow_minFac (k := 4) (by decide)).symm
  exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hDL).mp hnormal)
/-- The order-three actor acts nontrivially on the four-group. -/
public theorem exceptional_actor_not_centralizes_four (h : Janko1CentralizerData G)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3) :
    ¬ X ≤ centralizer (V : Set G) := by
  intro hXC
  have hd := card_dvd_of_le hXC
  rw [hX, h.four_centralizer_card V hV] at hd
  norm_num at hd

end CFSG.Quasithin.Janko1CentralizerData
