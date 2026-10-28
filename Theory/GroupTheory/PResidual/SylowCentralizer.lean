module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Residual supplements in a point centralizer

If a full Sylow subgroup T normalizes C, then O²(C)T = CT. Restrict T to
the join and use its Sylow intersection with the normal subgroup C.
If T fixes z and normalizes L, factoring each element of LT then gives
O²(C_L(z))T = C_{LT}(z). Normality is relative to the join, not ambient.

The source application identifies the literal XT in the tensor centralizer
setup, before taking its two-core S.
Source: Aschbacher--Smith 8.3, printed p.724.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem embedded_pResidual_sup_sylow_of_normalizes (T : Sylow 2 G) (C : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (C : Set G)) :
    (pResidual 2 C).map C.subtype ⊔ (T : Subgroup G) = C ⊔ (T : Subgroup G) := by
  let H := C ⊔ (T : Subgroup G)
  let C' := C.subgroupOf H
  have hCH : C ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  let S := T.subtype hTH
  let : C'.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hn)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal C'
  have hc := congrArg (fun A : Subgroup C' => A.map C'.subtype)
    (pResidual_sup_sylow_eq_top R)
  rw [map_sup,← MonoidHom.range_eq_map,range_subtype,hR,subgroupOf_map_subtype] at hc
  have hCT : C' ⊔ (S : Subgroup H) = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [map_sup,map_subgroupOf_eq_of_le hCH,← MonoidHom.range_eq_map,range_subtype]
    change C ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H
    rw [map_subgroupOf_eq_of_le hTH]
  have he : (pResidual 2 C').map C'.subtype ⊔ (S : Subgroup H) = ⊤ := by
    calc
      _ = ((pResidual 2 C').map C'.subtype ⊔ ((S : Subgroup H) ⊓ C')) ⊔
          (S : Subgroup H) := by
        exact le_antisymm (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
          (sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right)
      _ = C' ⊔ (S : Subgroup H) := congrArg (· ⊔ (S : Subgroup H)) hc
      _ = ⊤ := hCT
  have hh := congrArg (fun A : Subgroup H => A.map H.subtype) he
  rw [map_sup,map_embedded_pResidual,map_subgroupOf_eq_of_le hCH,
    ← MonoidHom.range_eq_map,range_subtype] at hh
  change (pResidual 2 C).map C.subtype ⊔
    ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
  rwa [map_subgroupOf_eq_of_le hTH] at hh

end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
open scoped Pointwise

theorem embedded_pointResidual_sup_sylow (T : Sylow 2 G) (L : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) (z : G)
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (pResidual 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({z} : Set G)).subtype ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z} : Set G) := by
  have hnorm : (T : Subgroup G) ≤ normalizer (L ⊓ centralizer ({z} : Set G) : Set G) :=
    (le_inf hn (hz.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [embedded_pResidual_sup_sylow_of_normalizes T _ hnorm]
  apply le_antisymm
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hz)
  · rintro g ⟨hg,hgz⟩
    have hm : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L _ hn]
      exact hg
    obtain ⟨l,hl,t,ht,rfl⟩ := hm
    have hlz := (centralizer ({z} : Set G)).mul_mem hgz
      ((centralizer ({z} : Set G)).inv_mem (hz ht))
    rw [mul_inv_cancel_right] at hlz
    exact mul_mem_sup ⟨hl,hlz⟩ ht

end Subgroup
