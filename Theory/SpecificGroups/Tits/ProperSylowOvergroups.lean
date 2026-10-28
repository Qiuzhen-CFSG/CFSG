module
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.ConverseLocalCores.First
public import Theory.SpecificGroups.Tits.ConverseLocalCores.Second
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
/-!
# Proper full-Sylow overgroups in the Tits group have characteristic two

The checked double-coset geometry places every proper overgroup of the
marked Sylow in one of the two full parabolics. Their self-centralizing
two-cores restrict to all intermediate Sylow overgroups. Conjugating the
original Sylow and transporting along the actual Parrott equivalence gives
the intrinsic characteristic-two bound on either original carrier.
Source: Parrott (1972), §5, p.683; Aschbacher–Smith A.3.12 and C.5.13.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Tits.ProperSylowOvergroups
open ExceptionalParabolics
/-- The bound on the actual finite permutation carrier. -/
theorem atlas_centralizer_twoCore_le (Q : Sylow 2 Atlas1600Group)
    (H : Subgroup Atlas1600Group) (hQH : (Q : Subgroup Atlas1600Group) ≤ H)
    (hH : H ≠ ⊤) : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Atlas1600Group Q atlas1600SylowTwo
  let e := MulAut.conj g
  let X := H.map e.toMonoidHom
  have hX : X ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact he
  have hSX : atlas1600SylowTwoSubgroup ≤ X := by
    have hh : (Q : Subgroup Atlas1600Group).map e.toMonoidHom = atlas1600SylowTwoSubgroup := by
      change ((g • Q : Sylow 2 Atlas1600Group) : Subgroup Atlas1600Group) = _
      rw [hg,atlas1600SylowTwo_coe]
    rw [← hh]
    exact map_mono hQH
  have hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
    rcases ConverseLocalCoverage.le_first_or_second X hX hSX with hf | hs
    · have hcore : pCore 2 first ≤ X.subgroupOf first :=
        (pCore_isPGroup.le_sylow_of_normal
          (atlas1600SylowTwo.subtype (by simpa only [atlas1600SylowTwo_coe] using hSX.trans hf))).trans
          (comap_mono (by simpa only [atlas1600SylowTwo_coe] using hSX))
      exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hf)).mp
        (centralizer_pCore_le_of_pCore_le _ ConverseLocalCores.first_core_self_centralizing hcore)
    · have hcore : pCore 2 second ≤ X.subgroupOf second :=
        (pCore_isPGroup.le_sylow_of_normal
          (atlas1600SylowTwo.subtype (by simpa only [atlas1600SylowTwo_coe] using hSX.trans hs))).trans
          (comap_mono (by simpa only [atlas1600SylowTwo_coe] using hSX))
      exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hs)).mp
        (centralizer_pCore_le_of_pCore_le _ ConverseLocalCores.second_core_self_centralizing hcore)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap H)).mpr hc

/-- The literal Parrott carrier used in the rank-two Theorem C list. -/
theorem centralizer_twoCore_le (Q : Sylow 2 ParrottGroup)
    (H : Subgroup ParrottGroup) (hQH : (Q : Subgroup ParrottGroup) ≤ H)
    (hH : H ≠ ⊤) : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let e := parrottFiniteImageEquiv
  have hne : H.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he,map_top_of_surjective e.toMonoidHom e.surjective]
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap H)).mpr
    (atlas_centralizer_twoCore_le (Q.mapSurjective e.surjective) (H.map e.toMonoidHom)
      (map_mono hQH) hne)
end Tits.ProperSylowOvergroups
