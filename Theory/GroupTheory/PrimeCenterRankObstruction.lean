module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.CommutatorPreimage

/-!
# A prime center and an outside actor force rank three

Let K be normal and have center of order p. An outside element of order p
centralizes that center, since the center is a normal subgroup of order p
in their p-group join. Those two independent cyclic groups contribute rank
two. If they normalize B ≤ K and centralize B modulo its two-core, a
centerless quotient B/O₂(B) of positive p-rank adds a third rank.

The argument retains relative normalization and commutation modulo O₂(B).
It does not replace quotient centralization by centralization of B.
Source application: Aschbacher–Smith, original 4.3.12(2), printed p.617,
and the cubic-center alternatives of A.3.18, pp.51–53.
-/

public section
open Subgroup
open Theory.GroupTheory.ResidualCentralizerRank
noncomputable section
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normal prime center and an outside prime actor obstruct ambient rank two
when the actor centralizes a positive-rank centerless section modulo its two-core. -/
theorem primeRank_three_of_prime_center_and_outside_actor (K B : Subgroup G) [K.Normal] (hBK : B ≤ K)
    (hZ : Nat.card (center K) = p)
    (hzB : center (B ⧸ pCore 2 B) = ⊥)
    (hrB : 1 ≤ primeRank p B) (ho : Odd p)
    (x : G) (hx : orderOf x = p) (hxK : x ∉ K)
    (hc : ⁅zpowers x, B⁆ ≤ B.pCoreIn 2) : 3 ≤ primeRank p G := by
  let Z := (center K).map K.subtype
  let X := zpowers x
  let A := Z ⊔ X
  have hzcard : Nat.card Z = p := by
    rw [card_map_of_injective K.subtype_injective]
    exact hZ
  let : Z.Normal := inferInstance
  have hzP : IsPGroup p Z := IsPGroup.of_card (n := 1) (by simpa using hzcard)
  have hxP : IsPGroup p X := IsPGroup.of_card (n := 1) (by simp [X, Nat.card_zpowers, hx])
  have hAP : IsPGroup p A := hzP.to_sup_of_normal_left hxP
  have hzsmall : Nat.card (Z.subgroupOf A) ∣ p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ A from le_sup_left)).toEquiv, hzcard]
  have hzcentral := hAP.normal_le_center_of_card_dvd_prime (Z.subgroupOf A) hzsmall
  have hZX : Z ≤ centralizer (X : Set G) := by
    intro z hz y hy
    have hh := mem_center_iff.mp (hzcentral (show (⟨z, (le_sup_left : Z ≤ A) hz⟩ : A) ∈ Z.subgroupOf A from hz))
      (⟨y, (le_sup_right : X ≤ A) hy⟩ : A)
    exact congrArg Subtype.val hh
  have hdis : Disjoint Z X :=
    (K.disjoint_zpowers_of_prime_order_not_mem x hx hxK).mono_left (map_subtype_le _)
  have hAr : 2 ≤ primeRank p A := by
    have he := Z.primeRank_sup_eq_add_of_disjoint_commuting X hdis hZX p
    have hzpos : primeRank p Z ≠ 0 := by
      intro hh
      exact PrimeRank.eq_zero_iff_not_dvd_card.mp hh (hzcard ▸ dvd_refl p)
    have hxpos : primeRank p X ≠ 0 := by
      intro hh
      exact PrimeRank.eq_zero_iff_not_dvd_card.mp hh (by simp [X, Nat.card_zpowers, hx])
    change 2 ≤ primeRank p (Z ⊔ X : Subgroup G)
    omega
  have hZB : Z ≤ centralizer (B : Set G) := by
    rintro z ⟨k, hk, rfl⟩ b hb
    exact congrArg K.subtype (mem_center_iff.mp hk ⟨b, hBK hb⟩)
  have hXB : X ≤ normalizer (B : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hc.trans (pCoreIn_le 2 B))
  have hAB : A ≤ normalizer (B : Set G) :=
    sup_le (hZB.trans (centralizer_le_normalizer _)) hXB
  have hcoreN : normalizer (B : Set G) ≤ normalizer (B.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hcomm : ⁅A, B⁆ ≤ B.pCoreIn 2 := by
    apply (commutator_mono (show A ≤ commutatorPreimage (normalizer (B : Set G)) B (B.pCoreIn 2) from ?_) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hcoreN)
    exact sup_le
      (le_commutatorPreimage (hZB.trans (centralizer_le_normalizer _))
        ((commutator_eq_bot_iff_le_centralizer.mpr hZB).le.trans bot_le))
      (le_commutatorPreimage hXB hc)
  have hr := (primeRank_sum_le_of_normalized_factor ho A B hAB
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcomm)
    (by rw [hzB, card_bot]; exact Nat.coprime_one_right p)).trans
      (primeRank_subgroup_le p (A ⊔ B : Subgroup G))
  omega
end Theory.GroupTheory
