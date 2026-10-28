module
public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Intersecting a residual factorization with a Sylow-containing subgroup

The source ordering factorization has the form `D = A ⊔ C`, where the
original Sylow group lies in `A`, while the two-residual of `C` lies in the
subgroup `H ≤ D` under consideration.  If `D` normalizes `C`, the Sylow
residual supplement first gives `D ≤ A ⊔ O²(C)`.  The perfect-factor
intersection identity then transports the residual through `H` and gives the
displayed product.  This is the group-theoretic lower layer used by the
Case-I normalization argument (source 15.1.18(3)).
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem pResidual_eq_sup_of_normal_perfect_factor (p : ℕ)
    (A R : Subgroup G) [R.Normal] (hR : IsPPerfect p R) (hgen : A ⊔ R = ⊤) :
    pResidual p G = (pResidual p A).map A.subtype ⊔ R := by
  let q := QuotientGroup.mk' R
  have hA : A.map q = ⊤ := by
    have hh := congrArg (map q) hgen
    simpa [map_sup, q, map_top_of_surjective _
      (QuotientGroup.mk'_surjective R)] using hh
  have he := pResidual_eq_embedded_sup_kernel_of_map_le p A q
    (by rw [hA]; exact le_top)
  rw [QuotientGroup.ker_mk', inf_eq_right.mpr
    (le_pResidual_of_isPPerfect R hR)] at he
  exact he

theorem embedded_pResidual_intersection_of_perfect_factor (p : ℕ)
    (A R H : Subgroup G) (hAR : A ≤ normalizer (R : Set G))
    (hR : IsPPerfect p R) (hRH : R ≤ H) (hcover : H ≤ A ⊔ R) :
    (pResidual p H).map H.subtype =
      (pResidual p (A ⊓ H : Subgroup G)).map (A ⊓ H).subtype ⊔ R := by
  have hgen : (A ⊓ H) ⊔ R = H := by
    apply le_antisymm (sup_le inf_le_right hRH)
    intro h hh
    have hm := hcover hh
    have he := coe_mul_of_left_le_normalizer_right A R hAR
    have hm' : h ∈ (A : Set G) * (R : Set G) := by
      rw [← he]
      exact hm
    obtain ⟨a, ha, r, hr, har⟩ := hm'
    have haH : a ∈ H := by
      have hx := H.mul_mem hh (H.inv_mem (hRH hr))
      simpa only [← har, mul_inv_cancel_right] using hx
    rw [← har]
    exact mul_mem_sup ⟨ha, haH⟩ hr
  let R' := R.subgroupOf H
  let A' := (A ⊓ H).subgroupOf H
  let : R'.Normal := normal_subgroupOf_of_le_normalizer
    (hcover.trans (sup_le hAR R.le_normalizer))
  have hp : IsPPerfect p R' := hR.of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom
    (subgroupOfEquivOfLe hRH).symm.surjective
  have hgen' : A' ⊔ R' = ⊤ := by
    change (A ⊓ H).subgroupOf H ⊔ R.subgroupOf H = ⊤
    rw [← subgroupOf_sup inf_le_right hRH, hgen, subgroupOf_self]
  have he := congrArg (map H.subtype)
    (pResidual_eq_sup_of_normal_perfect_factor p A' R' hp hgen')
  rw [map_sup, map_embedded_pResidual,
    show A'.map H.subtype = A ⊓ H from map_subgroupOf_eq_of_le inf_le_right,
    show R'.map H.subtype = R from map_subgroupOf_eq_of_le hRH] at he
  exact he

theorem embedded_pResidual_intersection_of_sylow_factor
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (D A C H : Subgroup G)
    (hD : D = A ⊔ C) (hTA : (T : Subgroup G) ≤ A)
    (hDC : D ≤ normalizer (C : Set G)) (hHD : H ≤ D)
    (hRH : (pResidual p C).map C.subtype ≤ H) :
    (pResidual p H).map H.subtype =
      (pResidual p (A ⊓ H : Subgroup G)).map (A ⊓ H).subtype ⊔
        (pResidual p C).map C.subtype := by
  let R := (pResidual p C).map C.subtype
  have hAD : A ≤ D := hD ▸ le_sup_left
  have hCR : C ≤ R ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T C
      (hTA.trans (hAD.trans hDC))
  have hDR : D ≤ A ⊔ R := by
    rw [hD]
    exact sup_le le_sup_left
      (hCR.trans (sup_le le_sup_right (hTA.trans le_sup_left)))
  apply embedded_pResidual_intersection_of_perfect_factor p A R H
    ((hAD.trans hDC).trans
      (normalizer_le_normalizer_characteristic_image C (pResidual p C)))
    (isPPerfect_embedded_pResidual p C) hRH (hHD.trans hDR)

end Subgroup
