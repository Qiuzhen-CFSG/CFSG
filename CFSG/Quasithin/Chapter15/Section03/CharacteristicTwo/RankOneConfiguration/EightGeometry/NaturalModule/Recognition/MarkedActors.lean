module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line

/-!
# The actors of the marked moving line

The image of the original Sylow subgroup is Sylow in the original star
quotient. The preliminary theta identity puts Y₊ inside M ∩ L. Relative
normality of L then makes S normalize that component parabolic; both
containment and normalization pass through the original star map.
Finally I = LS gives generation of the entire star quotient by the
component and the Sylow image. These facts supply the subgroup hypotheses
of the geometric exclusions without changing any marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27–28 and 15.3.32(1), printed pp.1130–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G]

/-- The image Sylow under the original action quotient. -/
noncomputable def starSylow [Finite G] (d : LocalData G) {I : Subgroup G}
    (P : Sylow 2 I) : Sylow 2 (d.Star I) :=
  P.mapSurjective (QuotientGroup.mk'_surjective _)

/-- Its underlying subgroup is the original marking of S. -/
theorem starSylow_coe [Finite G] (d : LocalData G) {I : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    (starSylow d P : Subgroup (d.Star I)) = d.starImage I d.S := by
  change (P : Subgroup I).map (d.starMap I) = (d.S.subgroupOf I).map (d.starMap I)
  congr 1
  apply map_injective I.subtype_injective
  rw [hP, map_subgroupOf_eq_of_le (hP ▸ map_subtype_le (P : Subgroup I))]

/-- The moving actor belongs to the component parabolic. -/
theorem LineData.yplus_star_le_parabolic (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (h : LineData d I) (hYL : d.Yplus ≤ c.L) :
    d.starImage I d.Yplus ≤ d.starImage I (d.M ⊓ c.L) := by
  apply map_mono
  apply comap_mono
  exact le_inf ((h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left) hYL

/-- Relative normality of L suffices for Sylow invariance of M ∩ L. -/
theorem component_parabolic_normalized_by_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S) :
    d.S ≤ normalizer (d.M ⊓ c.L : Subgroup G) := by
  have hLI : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  intro s hs
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact ⟨(d.M.le_normalizer ((inf_le_left.trans d.sylow_le) hs) x).mp hx.1,
      (hLI (hSI hs) x).mp hx.2⟩
  · intro hx
    exact ⟨((d.M.le_normalizer ((inf_le_left.trans d.sylow_le) hs)) x).mpr hx.1,
      (hLI (hSI hs) x).mpr hx.2⟩


/-- The original quotient retains the parabolic normalization. -/
theorem star_sylow_normalizes_parabolic (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S) :
    d.starImage I d.S ≤ normalizer (d.starImage I (d.M ⊓ c.L) : Set (d.Star I)) := by
  have hpI : d.M ⊓ c.L ≤ I := inf_le_right.trans (component_le c)
  have h : d.S.subgroupOf I ≤ normalizer ((d.M ⊓ c.L).subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hpI]
    exact comap_mono (component_parabolic_normalized_by_sylow d c hn hI)
  exact (map_mono h).trans (((d.M ⊓ c.L).subgroupOf I).le_normalizer_map (d.starMap I))

/-- The marked component and Sylow image generate the entire star actor. -/
theorem star_component_sup_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I = c.L ⊔ d.S) :
    d.starImage I c.L ⊔ d.starImage I d.S = ⊤ := by
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hj : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (component_le c),
      map_subgroupOf_eq_of_le hSI, ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm
  change (c.L.subgroupOf I).map (d.starMap I) ⊔
    (d.S.subgroupOf I).map (d.starMap I) = ⊤
  rw [← Subgroup.map_sup, hj]
  exact map_top_of_surjective (d.starMap I) (QuotientGroup.mk'_surjective _)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

end
