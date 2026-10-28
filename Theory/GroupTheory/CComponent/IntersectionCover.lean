module
public import Theory.GroupTheory.CComponent.SolvableSupplement

/-!
# C-components in covering intersections

If H covers a C-component L modulo a solvable normal subgroup N, then
(L ∩ H)^∞ is a C-component of H and L = (L ∩ H)^∞ (L ∩ N).
The auxiliary intersection (L N) ∩ H is subnormal in H. Solvable
supplement theory identifies its residual with the literal intersection
residual and supplies the covering equality.

This is the intersection step used in Aschbacher–Smith, 4.2.4, combined
manuscript of 1 March 2004, printed p.608, from A.3.3(2)–(4).
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup covering a C-component modulo a solvable normal subgroup contains
the component residual of its literal intersection, and that residual still covers. -/
theorem IsCComponent.intersection_residual_cover {L H : Subgroup G} (hL : L.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hcover : (L : Set G) ⊆ (H : Set G) * (N : Set G)) :
    (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H).IsCComponent ∧
      (L : Set G) =
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype : Set G) *
          (L ⊓ N : Subgroup G) := by
  let J := L ⊔ N
  let P := J ⊓ H
  let R := (solvableResidual P).map P.subtype
  let A := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hNJ : N ≤ J := le_sup_right
  have hPJ : P ≤ J := inf_le_left
  have hPH : P ≤ H := inf_le_right
  have hgen : N ⊔ P = J := by
    apply le_antisymm (sup_le hNJ hPJ)
    apply sup_le _ le_sup_left
    intro l hl
    obtain ⟨h, hh, n, hn, he⟩ := hcover hl
    have hhJ : h ∈ J := by
      have he' : h = l * n⁻¹ := by rw [← he]; simp
      rw [he']
      exact J.mul_mem ((show L ≤ J from le_sup_left) hl) (J.inv_mem (hNJ hn))
    rw [← he]
    exact (N ⊔ P).mul_mem ((show P ≤ N ⊔ P from le_sup_right) ⟨hhJ, hh⟩)
      ((show N ≤ N ⊔ P from le_sup_left) hn)
  have hresJ : (solvableResidual J).map J.subtype = L :=
    hL.solvableResidual_sup_eq N le_normalizer_of_normal
  have hresCompJ : (solvableResidual J).IsCComponent := by
    have he : solvableResidual J = L.subgroupOf J := by
      apply map_injective J.subtype_injective
      rw [hresJ, map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    rw [he]
    exact hL.subgroupOf le_sup_left
  have hresCompP : (solvableResidual P).IsCComponent :=
    residual_isCComponent_of_solvable_supplement_in J N P hNJ hPJ
      le_normalizer_of_normal hgen hresCompJ
  have hRL : R ≤ L := (map_solvableResidual_mono hPJ).trans_eq hresJ
  have hRH : R ≤ H := (map_subtype_le _).trans hPH
  have hRA : R = A := by
    apply le_antisymm
    · let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
      exact le_map_solvableResidual_of_isPerfect R (L ⊓ H) (le_inf hRL hRH)
    · exact map_solvableResidual_mono (inf_le_inf (show L ≤ J from le_sup_left) le_rfl)
  have hJsub : J.IsSubnormal := by
    have h := (hL.subnormal.quotient (K := N)).comap (QuotientGroup.mk' N)
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using h
  have hPsubH : (P.subgroupOf H).IsSubnormal := by
    have he : P.subgroupOf H = J.subgroupOf H := by
      ext h
      exact and_iff_left h.property
    rw [he]
    exact hJsub.subgroupOf
  have hRcompH : (R.subgroupOf H).IsCComponent := by
    let e := (subgroupOfEquivOfLe hPH).symm
    have h := (hresCompP.map_equiv e).map_subtype hPsubH
    have he : ((solvableResidual P).map e.toMonoidHom).map (P.subgroupOf H).subtype =
        R.subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le hRH, map_map, map_map]
      rfl
    rwa [he] at h
  change (A.subgroupOf H).IsCComponent ∧ (L : Set G) = (A : Set G) * (L ⊓ N : Subgroup G)
  refine ⟨hRA ▸ hRcompH, ?_⟩
  have hLRN : L ≤ R ⊔ N := by
    have h := map_solvableResidual_le_sup_residual_of_sup_eq J N P hNJ hPJ
      le_normalizer_of_normal hgen
    rwa [hresJ, sup_comm] at h
  apply Set.Subset.antisymm
  · intro l hl
    obtain ⟨r, hr, n, hn, he⟩ := mem_sup_of_normal_right.mp (hLRN hl)
    have hnL : n ∈ L := by
      have h := L.mul_mem (L.inv_mem (hRL hr)) hl
      rw [← he] at h
      simpa only [inv_mul_cancel_left] using h
    exact ⟨r, hRA ▸ hr, n, ⟨hnL, hn⟩, he⟩
  · rintro _ ⟨a, ha, n, hn, rfl⟩
    exact L.mul_mem (hRL (hRA.symm ▸ ha)) hn.1
end Subgroup
