module

public import Theory.GroupTheory.PGroup.NormalEightReduction
public import Theory.ElementaryAbelian.Join

/-!
# Central fours without normal elementary eights

A central elementary four contains every normal elementary binary subgroup
when there is no normal elementary subgroup of order at least eight. The
join of the two subgroups is normal and elementary; its order is divisible
by four and less than eight. In particular the central omega four is the
unique normal elementary four.

An elementary subgroup of order at least eight also supplies an involution
outside the center when the central omega subgroup has order four. Finally,
Burnside fusion separates the central elements of a Sylow subgroup whose
normalizer is the product of the Sylow subgroup and its centralizer.

These are the common reductions for Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3 and Lemma 5.1, pp.386 and 393–394, saved in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
They do not replace absence of normal elementary eights by an ambient rank
bound.
-/

open Subgroup

namespace Subgroup

/-- A central elementary four contains every normal elementary subgroup
in the absence of normal elementary eights. -/
public theorem normal_elementary_le_central_four_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (Z : Subgroup P) [IsElementaryAbelian 2 Z] (hZ : Nat.card Z = 4)
    (hZc : Z ≤ center P) (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] :
    E ≤ Z := by
  let : Z.Normal := ⟨by
    intro z hz g
    simpa only [mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right] using hz⟩
  let : IsElementaryAbelian 2 (Z ⊔ E : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (by
      intro e he z hz
      exact (mem_center_iff.mp (hZc hz) e).symm)
  have hlt : Nat.card (Z ⊔ E : Subgroup P) < 8 := by
    by_contra! h
    exact hno ⟨Z ⊔ E, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card (Z ⊔ E : Subgroup P) := by
    rw [← hZ]
    exact card_dvd_of_le le_sup_left
  have heq : Z = Z ⊔ E := eq_of_le_of_card_ge le_sup_left (by omega)
  exact heq ▸ le_sup_right

/-- If every involution is central, every elementary binary subgroup lies
in the first omega subgroup of the center. -/
public theorem elementary_le_omega_center_of_involutions_central
    {P : Type*} [Group P] [Finite P]
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hcentral : ∀ x : P, orderOf x = 2 → x ∈ center P) :
    A ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  intro x hx
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxc : x ∈ center P := by
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact hcentral x (orderOf_eq_prime hx2 hx1)
  refine ⟨⟨x, hxc⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  change (⟨x, hxc⟩ : center P) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa using hx2

/-- Every normal elementary subgroup lies in the central omega four. -/
public theorem normal_elementary_le_omega_center_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] :
    E ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let O := omega₁ (center P) (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 (O.map (center P).subtype) := IsElementaryAbelian.map _
  apply normal_elementary_le_central_four_of_no_normal_eight hno
    (O.map (center P).subtype) _ (map_subtype_le _) E
  rwa [card_map_of_injective (center P).subtype_injective]

/-- The central omega four is the unique normal elementary four. -/
public theorem normal_four_eq_omega_center_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    E = (omega₁ (center P) (p := 2)).map (center P).subtype := by
  apply eq_of_le_of_card_ge (normal_elementary_le_omega_center_of_no_normal_eight hno hZ E)
  rw [card_map_of_injective (center P).subtype_injective, hZ, hE]

/-- An elementary subgroup of rank at least three forces a noncentral
involution when the central omega has order four. -/
public theorem exists_noncentral_involution_of_rank_three_of_omega_center_four
    {P : Type*} [Group P] [Finite P]
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    ∃ x : P, orderOf x = 2 ∧ x ∉ center P := by
  by_contra! h
  have hle := card_le_of_le (elementary_le_omega_center_of_involutions_central A h)
  rw [card_map_of_injective (center P).subtype_injective, hZ] at hle
  omega

end Subgroup

namespace Sylow

/-- The Sylow-normalizer product condition separates central elements
under ambient conjugacy. No rank bound or simplicity assumption is used. -/
public theorem eq_of_isConj_of_mem_center_of_normalizer_eq
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hN : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G))
    (z t : S) (hz : z ∈ center S) (ht : t ∈ center S)
    (hc : IsConj (z : G) (t : G)) : z = t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hzC : (z : G) ∈ centralizer (S : Set G) := by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨x, hx⟩ : S))
  have htC : (t : G) ∈ centralizer (S : Set G) := by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp ht (⟨x, hx⟩ : S))
  obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer (z : G) g⁻¹
    hzC (by simpa only [inv_inv, hg] using htC)
  have hfix : (S : Subgroup G) ⊔ centralizer (S : Set G) ≤
      centralizer ({(z : G)} : Set G) := by
    apply sup_le
    · intro s hs
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hz (⟨s, hs⟩ : S)))
    · intro c hc
      exact mem_centralizer_singleton_iff.mpr (hc z z.property).symm
  have hcomm := mem_centralizer_singleton_iff.mp (hfix (hN ▸ hn))
  have heq : (t : G) = z := by
    rw [show (t : G) = n⁻¹ * (z : G) * n from
      (by simpa only [inv_inv, hg] using he), mul_assoc, ← hcomm, inv_mul_cancel_left]
  exact (Subtype.ext heq).symm

end Sylow
