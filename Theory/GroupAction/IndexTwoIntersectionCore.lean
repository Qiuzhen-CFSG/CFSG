module
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The intersection of the two conjugates in an index-two overgroup

If T has index two in M and normalizes D, an element x outside T has exactly
the two conjugates D and Dˣ. Their intersection is therefore M-normalized.
The proof uses the two cosets and x²∈T directly and works for arbitrary D
in the ambient group. Its C.5 application combines this normality with the
original no-common-normal-subgroup hypothesis to obtain D∩Dˣ=1.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–159.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem index_two_conjugate_intersection_normalized
    (M T D : Subgroup G) (hTM : T ≤ M) (hindex : T.relIndex M = 2)
    (hTD : T ≤ normalizer (D : Set G))
    (x : G) (hx : x ∈ M) (hxT : x ∉ T) :
    M ≤ normalizer ((D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  let e := MulAut.conj x⁻¹
  let D' := D.map e.toMonoidHom
  let P := D ⊓ D'
  change M ≤ normalizer (P : Set G)
  have hnorm : (T.subgroupOf M).Normal := normal_of_index_eq_two hindex
  have hMT : M ≤ normalizer (T : Set G) := (normal_subgroupOf_iff_le_normalizer hTM).mp hnorm
  have hTmap : T.map e.toMonoidHom = T := mem_normalizer_iff_map_conj_eq.mp (hMT (M.inv_mem hx))
  have hTD' : T ≤ normalizer (D' : Set G) := by
    rw [← hTmap]
    exact (map_mono hTD).trans (le_normalizer_map e.toMonoidHom)
  have hTP : T ≤ normalizer (P : Set G) := (le_inf hTD hTD').trans inf_normalizer_le_normalizer_inf
  have hx2 : x ^ 2 ∈ T := by
    exact sq_mem_of_index_two hindex (⟨x, hx⟩ : M)
  have hDD : D'.map e.toMonoidHom = D := by
    change (D.map e.toMonoidHom).map e.toMonoidHom = D
    rw [map_map]
    have he : e.toMonoidHom.comp e.toMonoidHom = (MulAut.conj ((x ^ 2)⁻¹)).toMonoidHom := by
      ext d
      simp [e, pow_two, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hTD (T.inv_mem hx2))
  have hxP : x ∈ normalizer (P : Set G) := by
    have he : P.map e.toMonoidHom = P := by
      change (D ⊓ D').map e.toMonoidHom = D ⊓ D'
      rw [map_inf _ _ _ e.injective, hDD]
      exact inf_comm _ _
    have hh : x⁻¹ ∈ normalizer (P : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    simpa only [inv_inv] using (normalizer (P : Set G)).inv_mem hh
  intro g hg
  by_cases hgT : g ∈ T
  · exact hTP hgT
  · have hm : g * x⁻¹ ∈ T := by
      exact (mul_mem_iff_of_index_two hindex (a := (⟨g, hg⟩ : M))
        (b := (⟨x⁻¹, M.inv_mem hx⟩ : M))).mpr
        (iff_of_false hgT (fun hi => hxT (by
          have hi' : x⁻¹ ∈ T := hi
          simpa only [inv_inv] using T.inv_mem hi')))
    have hh := (normalizer (P : Set G)).mul_mem (hTP hm) hxP
    simpa using hh
end Subgroup
