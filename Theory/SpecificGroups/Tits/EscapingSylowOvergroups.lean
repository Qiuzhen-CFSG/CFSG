module

public import Theory.SpecificGroups.Tits.SylowCenterMaximal
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Geometry
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The escaping Tits Sylow overgroup

The first parabolic is the centralizer of the full Sylow center. Its
relative Sylow normalizer therefore gives the ambient Sylow normalizer.
The certified proper-overgroup coverage puts any subgroup escaping the
first parabolic in the second. The Sylow subgroup has index three there,
so a proper escaping overgroup is exactly the second parabolic, which is
maximal by generation and the same coverage.

The final transport retains the caller's original Sylow and actual model
isomorphism. It supplies the other maximal parabolic in ordinary 15.1.22(4)
once the original cubic action proves escape.
Source: Parrott (1972), §5, p.683; Aschbacher--Smith, printed pp.1098--1099,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory

namespace Tits.BinarySylowOvergroups
open ExceptionalParabolics

theorem normalizer_eq : normalizer (S : Set Atlas1600Group) = S := by
  apply le_antisymm _ S.le_normalizer
  intro x hx
  have he := RelativeParabolicNormalizers.fixes_r5 (MulAut.conj x)
    ((mem_normalizer_iff_map_conj_eq).mp hx)
  have hxF : x ∈ first := by
    rw [RelativeParabolicNormalizers.first_eq_centralizer]
    apply mem_centralizer_singleton_iff.mpr
    exact mul_inv_eq_iff_eq_mul.mp he
  have hh := le_normalizer_comap first.subtype
    (show (⟨x,hxF⟩ : first) ∈ (normalizer (S : Set Atlas1600Group)).comap first.subtype from hx)
  change (⟨x,hxF⟩ : first) ∈ normalizer (S.subgroupOf first : Set first) at hh
  rw [first_sylow_normalizer] at hh
  exact hh

theorem second_isCoatom : IsCoatom second := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨ConverseLocalCoverage.twoLocal_ne_top second ConverseLocalCoverage.second_isTwoLocal, ?_⟩
  intro H hH hSH
  rcases ConverseLocalCoverage.le_first_or_second H hH (sylow_le_second.trans hSH) with hf | hs
  · have ht : (⊤ : Subgroup Atlas1600Group) ≤ first :=
      generate ▸ sup_le le_rfl (hSH.trans hf)
    exact (ConverseLocalCoverage.twoLocal_ne_top first
      ConverseLocalCoverage.first_isTwoLocal (top_unique ht)).elim
  · exact hs

theorem escaping_overgroup_eq_second (H : Subgroup Atlas1600Group) (hH : H ≠ ⊤)
    (hSH : S ≤ H) (hout : ¬ H ≤ first) : H = second := by
  have hH2 := (ConverseLocalCoverage.le_first_or_second H hH hSH).resolve_left hout
  have hmax := isCoatom_of_index_three (S.subgroupOf second) second_sylow_index
  rcases hmax.le_iff.mp (comap_mono hSH : S.subgroupOf second ≤ H.subgroupOf second) with ht | he
  · exact le_antisymm hH2 (subgroupOf_eq_top.mp ht)
  · have he' := congrArg (map second.subtype) he
    change (H.subgroupOf second).map second.subtype = (S.subgroupOf second).map second.subtype at he'
    rw [map_subgroupOf_eq_of_le hH2, map_subgroupOf_eq_of_le sylow_le_second] at he'
    exact (hout (he' ▸ sylow_le_first)).elim
end Tits.BinarySylowOvergroups

namespace Tits.BinarySylowOvergroups
open ExceptionalParabolics
private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- The actual Sylow marking identifies every proper escaping overgroup
with the second Tits parabolic; in particular it is maximal. -/
theorem sylow_geometry {K : Type*} [Group K]
    (e : K ≃* ParrottGroup) (P : Sylow 2 K) :
    normalizer (P : Set K) = P ∧
      IsCoatom (centralizer ((center P).map (P : Subgroup K).subtype : Set K)) ∧
      ∀ H : Subgroup K, H ≠ ⊤ → (P : Subgroup K) ≤ H →
        ¬ H ≤ centralizer ((center P).map (P : Subgroup K).subtype : Set K) → IsCoatom H := by
  obtain ⟨f,hf⟩ := RelativeSylowMarking.exists_sylow_marking
    (e.trans parrottFiniteImageEquiv) P
  have hZ : ((center P).map (P : Subgroup K).subtype).map f.toMonoidHom =
      (center atlas1600SylowTwoSubgroup).map atlas1600SylowTwoSubgroup.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup K) f.toMonoidHom f.injective, hf]
  have hC : (centralizer ((center P).map (P : Subgroup K).subtype : Set K)).map
      f.toMonoidHom = first := by
    rw [centralizer_map_equiv, hZ, SylowCenterMaximal.standard_centralizer]
  refine ⟨?_,SylowCenterMaximal.centralizer_isCoatom e P,?_⟩
  · apply map_injective (f := f.toMonoidHom) f.injective
    calc
      _ = normalizer (((P : Subgroup K).map f.toMonoidHom) : Set Atlas1600Group) :=
        map_equiv_normalizer_eq (P : Subgroup K) f
      _ = _ := by rw [hf]; exact normalizer_eq
  · intro H hH hPH hout
    apply (f.mapSubgroup.isCoatom_iff H).mp
    change IsCoatom (H.map f.toMonoidHom)
    rw [escaping_overgroup_eq_second (H.map f.toMonoidHom) ?_ ?_ ?_]
    · exact second_isCoatom
    · intro he
      apply hH
      apply map_injective (f := f.toMonoidHom) f.injective
      change H.map f.toMonoidHom = ⊤ at he
      exact he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
    · change atlas1600SylowTwoSubgroup ≤ H.map f.toMonoidHom
      rw [← hf]
      exact map_mono hPH
    · rw [← hC]
      intro hh
      exact hout ((f.mapSubgroup.le_iff_le).mp hh)
end Tits.BinarySylowOvergroups
