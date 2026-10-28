module

public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion

/-!
# Characteristic subgroups of the centralizer of a fused normal four

If the unique normal four of a Sylow two-subgroup is fused, its centralizer
has no characteristic subgroup of order two. Such a subgroup would be
normal in the Sylow, hence central, and its involution would belong to the
normal four. The automorphisms induced by fusion move this involution to
each of the other two, contradicting characteristicity.

Only normal elementary eights are excluded. Characteristic elementary
subgroups of the centralizer inherit that exclusion. These are local
structural inputs for the recognition alternatives in Janko–Thompson,
Math. Z. 113 (1970), 1.3–1.4, printed p.386.
-/

open Subgroup

namespace Sylow

variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of the unique fused normal four has no characteristic
subgroup of order two, without an elementary-rank bound. -/
public theorem centralizer_fused_four_no_characteristic_two
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G))
    (K : Subgroup (centralizer (W : Set S))) [K.Characteristic] : Nat.card K ≠ 2 := by
  let C := centralizer (W : Set S)
  have hi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ W hW
  let : C.Normal := normal_of_index_eq_two hi
  intro hK
  let L := K.map C.subtype
  let : L.Normal := ConjAct.normal_of_characteristic_of_normal
  have hL : Nat.card L = 2 := (card_map_of_injective C.subtype_injective).trans hK
  have hLc := central_of_normal_card_two L hL
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hK])
  let z : S := (a.val : C)
  have hz : orderOf z = 2 := (orderOf_coe (a.val : C)).trans ((orderOf_coe a).trans ha)
  have hzc : z ∈ center S := hLc (mem_map_of_mem C.subtype a.property)
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    ⟨⟨z, hzc⟩, subset_closure (by
      apply Subtype.ext
      change z ^ (2 ^ 1) = 1
      simpa only [pow_one, hz] using pow_orderOf_eq_one z), rfl⟩
  have hnot : ¬ W ≤ L := by
    intro h
    have hh := card_le_of_le h
    omega
  obtain ⟨x, hxW, hxL⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  let xC : C := ⟨x, le_centralizer W hxW⟩
  have hx : orderOf xC = 2 := (orderOf_coe xC).symm.trans
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxW) hx1)
  obtain ⟨f, hf⟩ := S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique z hz hzc hfused a.val xC hzW hxW
    ((orderOf_coe a).trans ha) hx
  have hfa : f a.val ∈ K := characteristic_iff_le_comap.mp inferInstance f a.property
  rw [hf] at hfa
  exact hxL (mem_map_of_mem C.subtype hfa)

omit [Finite G] in
/-- A characteristic elementary subgroup of the normal-four centralizer
cannot have order at least eight under the normal-only bound. -/
public theorem centralizer_four_characteristic_elementary_card_lt_eight
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (W : Subgroup S) [W.Normal]
    (K : Subgroup (centralizer (W : Set S))) [K.Characteristic]
    [IsElementaryAbelian 2 K] : Nat.card K < 8 := by
  let C := centralizer (W : Set S)
  let L := K.map C.subtype
  have hLn : L.Normal := ConjAct.normal_of_characteristic_of_normal
  have hLe : IsElementaryAbelian 2 L := IsElementaryAbelian.map_subtype
  by_contra! h
  apply hno ⟨L, hLn, hLe, ?_⟩
  simpa only [L, card_map_of_injective C.subtype_injective] using h

end Sylow
