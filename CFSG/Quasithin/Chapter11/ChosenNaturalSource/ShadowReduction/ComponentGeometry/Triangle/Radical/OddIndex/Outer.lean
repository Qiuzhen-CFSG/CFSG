module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Extension

/-!
# Separating the component contribution to the radical index

Let K be normal in J, and let R be Sylow in O∞(J). Restriction gives
R intersect K Sylow in O∞(K). If the Fitting index in K is two, its image
modulo O₂(J) has order two, since O₂(K) = K intersect O₂(J).
The subgroup product formula therefore gives

  [R : O₂(J)] = 2 [R : R intersect (K O₂(J))].

Thus the component contributes exactly a factor two; the remaining factor
measures radical elements outside K O₂(J). OddIndex.Source applies this
to the literal original R₁ and KT. It does not assert that the second
factor is one; that geometric step stays with the triangle assembly owner.
Source: the index step in Aschbacher–Smith 11.4.1(3), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

private theorem radical_fitting_quotient_isTwoGroup_of_index_two
    (hi : (twoFittingCore G).relIndex (solvableRadical G) = 2) :
    IsPGroup 2 (solvableRadical (G ⧸ twoFittingCore G)) := by
  let q := QuotientGroup.mk' (twoFittingCore G)
  let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have he : (solvableRadical G).map q = solvableRadical (G ⧸ twoFittingCore G) := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  apply IsPGroup.of_card (n := 1)
  rw [← he, ← relIndex_ker, QuotientGroup.ker_mk', hi, pow_one]

/-- Restrict a radical Sylow subgroup along the actual normal inclusion. -/
theorem sylow_radical_subgroupOf_normal (K R : Subgroup G) [K.Normal]
    (hs : Chapter1.IsSylowIn 2 R (solvableRadical G)) :
    Chapter1.IsSylowIn 2 (R.subgroupOf K) (solvableRadical K) := by
  have hrad : (solvableRadical K).map K.subtype = solvableRadical G ⊓ K := by
    rw [← radical_subgroupOf_normal K, subgroupOf_map_subtype]
  have hn : ((K ⊓ solvableRadical G).subgroupOf (solvableRadical G)).Normal := inferInstance
  have hh := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs
    (show K ⊓ solvableRadical G ≤ solvableRadical G from inf_le_right) hn.isSubnormal
  have hR : R ≤ solvableRadical G := (Chapter1.isSylowIn_iff.mp hs).2.1
  have he : R ⊓ (K ⊓ solvableRadical G) = R ⊓ K := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hR))
  rw [he] at hh
  apply (Chapter1.IsSylowIn.map_iff K.subtype K.subtype_injective).mp
  rw [subgroupOf_map_subtype, hrad, inf_comm (solvableRadical G) K]
  exact hh

/-- The exact factor two leaves only the image outside the component and core. -/
theorem radical_core_index_factor (K R : Subgroup G) [K.Normal]
    (hs : Chapter1.IsSylowIn 2 R (solvableRadical G))
    (hi : (twoFittingCore K).relIndex (solvableRadical K) = 2) :
    (pCore 2 G).relIndex R = 2 * (K ⊔ pCore 2 G).relIndex R := by
  have hk := fitting_index_eq_sylow_core_index (R.subgroupOf K)
    (sylow_radical_subgroupOf_normal K R hs)
    (radical_fitting_quotient_isTwoGroup_of_index_two hi)
  rw [hi, pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal,
    relIndex_comap, subgroupOf_map_subtype] at hk
  have hQR : pCore 2 G ≤ R := by
    let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    have hq := le_solvableRadical (pCore 2 G) inferInstance inferInstance
    obtain ⟨P,hP⟩ := hs
    have hl := (show IsPGroup 2 ((pCore 2 G).subgroupOf (solvableRadical G)) from
      pCore_isPGroup.comap_subtype).le_sylow_of_normal P
    rw [← hP]
    intro x hx
    exact ⟨⟨x,hq hx⟩,hl hx,rfl⟩
  have hd : (K ⊔ pCore 2 G) ⊓ R = (K ⊓ R) ⊔ pCore 2 G := by
    apply le_antisymm
    · rintro x ⟨hx,hR⟩
      obtain ⟨k,hk,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hx
      have hkr : k ∈ R := by simpa only [mul_inv_cancel_right] using R.mul_mem hR (R.inv_mem (hQR hq))
      exact mul_mem_sup ⟨hk,hkr⟩ hq
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right hQR)
  have hm := relIndex_inf_mul_relIndex (pCore 2 G) (K ⊔ pCore 2 G) R
  rw [inf_eq_left.mpr (show pCore 2 G ≤ K ⊔ pCore 2 G from le_sup_right), hd,
    relIndex_sup_right, inf_comm K R, ← hk] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
