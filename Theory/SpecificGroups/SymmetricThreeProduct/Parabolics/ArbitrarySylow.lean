module

public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The digon product at an arbitrary Sylow subgroup

The two distinct maximal Sylow overgroups are a conjugate of the coordinate
parabolics, in one of the two orders. Each has index three and their setwise
product is the whole group. The unordered model classification is used
without imposing an orientation on the source parabolics.

Source: Aschbacher–Smith I.5.3(4–5), printed p.420.
-/

public section
namespace SymmetricThreeProduct
open Subgroup

theorem distinct_coatoms_product (T : Sylow 2 G) (P R : Subgroup G)
    (hP : IsCoatom P) (hR : IsCoatom R)
    (hTP : (T : Subgroup G) ≤ P) (hTR : (T : Subgroup G) ≤ R) (hne : P ≠ R) :
    P.index = 3 ∧ R.index = 3 ∧ ∀ x : G, ∃ p ∈ P, ∃ r ∈ R, p * r = x := by
  obtain ⟨g, _, h⟩ := coatom_over_sylow T
  let e := MulAut.conj g
  have hidx (U : Subgroup G) (hu : U = e.mapSubgroup leftParabolic ∨
      U = e.mapSubgroup rightParabolic) : U.index = 3 := by
    rcases hu with rfl | rfl
    · exact (leftParabolic.index_map_equiv e).trans index_leftParabolic
    · exact (rightParabolic.index_map_equiv e).trans index_rightParabolic
  have hp := (h P).mp ⟨hP, hTP⟩
  have hr := (h R).mp ⟨hR, hTR⟩
  refine ⟨hidx P hp, hidx R hr, ?_⟩
  have hprod (x : G) : ∃ p ∈ e.mapSubgroup leftParabolic,
      ∃ r ∈ e.mapSubgroup rightParabolic, p * r = x := by
    obtain ⟨p, hp, r, hr, he⟩ := parabolics_product (e.symm x)
    refine ⟨e p, mem_map.mpr ⟨p, hp, rfl⟩, e r, mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    rw [← map_mul, he, e.apply_symm_apply]
  rcases hp with hp | hp <;> rcases hr with hr | hr
  · exact (hne (hp.trans hr.symm)).elim
  · simpa only [hp, hr] using hprod
  · intro x
    obtain ⟨p, hp', r, hr', he⟩ := hprod x⁻¹
    refine ⟨r⁻¹, hp ▸ (e.mapSubgroup rightParabolic).inv_mem hr',
      p⁻¹, hr ▸ (e.mapSubgroup leftParabolic).inv_mem hp', ?_⟩
    rw [← mul_inv_rev, he, inv_inv]
  · exact (hne (hp.trans hr.symm)).elim

end SymmetricThreeProduct
