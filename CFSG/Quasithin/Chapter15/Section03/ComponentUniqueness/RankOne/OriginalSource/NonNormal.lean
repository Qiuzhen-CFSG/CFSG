module

public import Theory.Quasithin.CoprimeRank
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.OriginalOrbit
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.Geometry

/-!
# Inner action from the moving component orbit

Positive cubic rank and the original nonnormal component catalogue identify
the Sylow orbit with the cubic residual. Its theta identity gives precisely
the inner-action conclusion needed by the actual rank-one reduction.

Source: Aschbacher--Smith 1.2.2 and 15.3.43, pp.505,1139.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The nonnormal component orbit supplies the literal prime-to-three
residual, hence the first source alternative and inner action. -/
theorem inner_of_original_nonnormal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.Hplus) (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (hn : ¬ d.S ≤ normalizer (L : Set G)) :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) := by
  obtain ⟨localSetup, planes⟩ := original_local_geometry d hI h hshadow
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let e := subgroupOfEquivOfLe h.component_le
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  have hzL : center L = pCore 2 L :=
    Subgroup.map_injective L.subtype_injective h.component_center
  have hlt : L < localSpan L d.S := lt_of_le_of_ne (le_conjugateSpanBy L d.S) (by
    intro he
    exact hn (he.symm ▸ le_normalizer_conjugateSpanBy L d.S))
  have hzK := component_center_eq_twoCore h.component h.outside_structure.odd_core
  let : IsSimpleGroup ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) :=
    ((QuotientGroup.quotientMulEquivOfEq hzK).isSimpleGroup_congr).mp IsQuasisimple.simple
  let : IsQuasisimple ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) :=
    IsQuasisimple.of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 (L.subgroupOf I)))
  have hqrank : 1 ≤ primeRank 3 ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_equiv 3 e]
    exact h.component_rank
  have hd : 3 ∣ Nat.card ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) := by
    by_contra hn
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  have hres := Candidates.source_threeResidual_eq_nonnormal_orbit hG d hI
    h.component_le (component_isCComponent h.component) hd hlt
  have halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S) :=
    Or.inl ⟨Candidates.yplus_le_theta_of_local h.outside_structure.theta_eq.symm,
      Candidates.theta_eq_orbit_of_threeResidual hzL.le h.component_rank
        h.component_le localSetup.sylow_le_overgroup hres⟩
  exact (localSetup.inner_of_alternatives d planes halt).1

end CFSG.Quasithin.Chapter15.Section03.RankOne
