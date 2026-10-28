module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Rejection

/-!
# Order and normal elementary abelian subgroups of the concrete HS two-subgroup

The explicit words enumerate the subgroup, with an inverse read from two point
images. Any element of a normal elementary abelian subgroup squares to one and
commutes with each of its conjugates. The checked rejection witnesses reduce
such elements to the eight products of the three elementary generators.
Products of their conjugates then give exactly the three initial subgroups.

All conclusions concern the specified degree-100 ATLAS carrier. The intrinsic
normality assumption is inside `subgroup`; its image is compared in `Carrier`.
Source: GLS volume 3, Table 5.3m, printed p.274; Aschbacher–Smith, condition E,
printed pp.3–4. The finite witnesses and their reproduction script are retained
in `SylowCatalogue/source/`. No local-cover or subgroup-catalogue premise is used.
-/

namespace Sporadic.LeechRelated.HS.EvenLocalCandidates
open Subgroup SylowCatalogueData

private theorem catalogue_of_small (H : Subgroup Carrier) (hH : H ≠ ⊥)
    (hn : ∀ x ∈ H, ∀ g ∈ subgroup, g * x * g⁻¹ ∈ H)
    (hsmall : ∀ x ∈ H, ∃ j : Fin 8, small j = x) :
    ∃ i : Fin 3, H = elementary i := by
  classical
  have hupper (i : Fin 3) (hi : ∀ j : Fin 8, small j ∈ H → j.val < 2 ^ (i.val + 1)) :
      H ≤ elementary i := by
    intro x hx
    obtain ⟨j, rfl⟩ := hsmall x hx
    exact small_mem_elementary j i (hi j hx)
  have hlower (i : Fin 3) {j : Fin 8} (hj : small j ∈ H)
      (hji : 2 ^ i.val ≤ j.val) : elementary i ≤ H := by
    apply (closure_le _).mpr
    rintro x ⟨k, hk, rfl⟩
    exact initial_le_of_small_mem H hn hj k
      ((Nat.pow_le_pow_right (by decide : 0 < 2) hk).trans hji)
  by_cases h2 : ∃ j : Fin 8, small j ∈ H ∧ 4 ≤ j.val
  · obtain ⟨j, hj, hj2⟩ := h2
    exact ⟨2, le_antisymm (hupper 2 (fun j _ => j.isLt)) (hlower 2 hj hj2)⟩
  by_cases h1 : ∃ j : Fin 8, small j ∈ H ∧ 2 ≤ j.val
  · obtain ⟨j, hj, hj1⟩ := h1
    refine ⟨1, le_antisymm (hupper 1 ?_) (hlower 1 hj hj1)⟩
    intro k hk
    change k.val < 4
    exact Nat.lt_of_not_ge (fun hk2 => h2 ⟨k, hk, hk2⟩)
  · obtain ⟨x, hx, hx1⟩ := H.bot_or_exists_ne_one.resolve_left hH
    obtain ⟨j, rfl⟩ := hsmall x hx
    have hj : 1 ≤ j.val := by
      by_contra h
      have hj0 : j = 0 := Fin.ext (by omega)
      exact hx1 (hj0 ▸ rfl)
    refine ⟨0, le_antisymm (hupper 0 ?_) (hlower 0 hx hj)⟩
    intro k hk
    change k.val < 2
    exact Nat.lt_of_not_ge (fun hk1 => h1 ⟨k, hk, hk1⟩)

/-- The exact candidate subgroup has order `2^9`. -/
public theorem subgroup_card : Nat.card subgroup = 2 ^ 9 :=
  SylowCatalogueData.subgroup_card

/-- Every nontrivial normal elementary abelian subgroup of the specified
HS two-subgroup maps to one of the three specified elementary candidates. -/
public theorem normal_elementary_catalogue (R : Subgroup subgroup) (hR : R ≠ ⊥)
    (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    ∃ i : Fin 3, R.map subgroup.subtype = elementary i := by
  let H := R.map subgroup.subtype
  let : IsElementaryAbelian 2 R := he
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.map_subtype
  have hH : H ≠ ⊥ := fun h => hR ((Subgroup.map_eq_bot_iff_of_injective
    (H := R) Subtype.val_injective).mp h)
  have hHS : H ≤ subgroup := Subgroup.map_subtype_le R
  have hnormal : ∀ x ∈ H, ∀ g ∈ subgroup, g * x * g⁻¹ ∈ H := by
    intro x hx g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr
      ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : subgroup)⁻¹,
        hn.conj_mem y hy ⟨g, hg⟩, rfl⟩
  apply catalogue_of_small H hH hnormal
  intro x hx
  exact small_of_normal_elementary_element x (hHS hx)
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (fun g hg => setLike_mul_comm hx (hnormal x hx g hg))

end Sporadic.LeechRelated.HS.EvenLocalCandidates
