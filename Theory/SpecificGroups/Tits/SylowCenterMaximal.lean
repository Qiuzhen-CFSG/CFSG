module
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.SylowPointwiseInner
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# Maximal Sylow-center centralizers in the Tits group

The certified proper-Sylow-overgroup coverage and generation of the two
parabolics prove maximality of the first parabolic. Its involution-centralizer
identification and the exact Sylow center identify it with the centralizer
of that center. Sylow conjugacy transports the result to any actual model
and the caller's original Sylow subgroup.

Source: Parrott (1972), §5, p.683; Aschbacher--Smith 15.1.20(3c),
printed pp.1096--1097. This is used by the original ordinary Tits row.
-/

public section
open Subgroup
namespace Tits.SylowCenterMaximal
open ExceptionalParabolics

/-- The first full Tits parabolic is a maximal proper subgroup. -/
theorem first_isCoatom : IsCoatom first := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨ConverseLocalCoverage.twoLocal_ne_top first ConverseLocalCoverage.first_isTwoLocal, ?_⟩
  intro H hH hFH
  rcases ConverseLocalCoverage.le_first_or_second H hH (sylow_le_first.trans hFH) with hf | hs
  · exact hf
  · have ht : (⊤ : Subgroup Atlas1600Group) ≤ second :=
      generate ▸ sup_le (hFH.trans hs) le_rfl
    exact (ConverseLocalCoverage.twoLocal_ne_top second
      ConverseLocalCoverage.second_isTwoLocal (top_unique ht)).elim

/-- The centralizer of the full marked Sylow center is the first parabolic. -/
theorem standard_centralizer :
    centralizer ((center atlas1600SylowTwoSubgroup).map
      atlas1600SylowTwoSubgroup.subtype : Set Atlas1600Group) = first := by
  rw [RelativeParabolicNormalizers.first_eq_centralizer]
  apply le_antisymm
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (hx atlas1600R5 (mem_map_of_mem _ atlas1600R5_mem_center_sylowTwo)).symm
  · intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hy
    change (z : Atlas1600Group) * x = x * z
    rcases (atlas1600SylowTwo_mem_center_iff z).mp hz with he | he
    · simp only [he, one_mul, mul_one]
    · rw [he]
      exact (mem_centralizer_singleton_iff.mp hx).symm

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- Maximality holds for every actual model and the originally supplied Sylow. -/
theorem centralizer_isCoatom {K : Type*} [Group K]
    (e : K ≃* ParrottGroup) (P : Sylow 2 K) :
    IsCoatom (centralizer ((center P).map (P : Subgroup K).subtype : Set K)) := by
  obtain ⟨f,hf⟩ := RelativeSylowMarking.exists_sylow_marking
    (e.trans parrottFiniteImageEquiv) P
  have hZ : ((center P).map (P : Subgroup K).subtype).map f.toMonoidHom =
      (center atlas1600SylowTwoSubgroup).map atlas1600SylowTwoSubgroup.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup K) f.toMonoidHom f.injective, hf]
  have hC : (centralizer ((center P).map (P : Subgroup K).subtype : Set K)).map
      f.toMonoidHom = first := by
    rw [centralizer_map_equiv, hZ, standard_centralizer]
  apply (f.mapSubgroup.isCoatom_iff _).mp
  change IsCoatom ((centralizer ((center P).map (P : Subgroup K).subtype : Set K)).map f.toMonoidHom)
  rw [hC]
  exact first_isCoatom

end Tits.SylowCenterMaximal
