module
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.Fitting.Subgroup
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# The faithful almost-simple reduction for the M₁₂ value bound

If F*(G) is nonabelian simple, its Fitting subgroup is trivial. The Fitting
subgroup of the solvable radical then shows that the radical is trivial too.
A nontrivial centralizer would supply a second commuting component. This
component lies in F*(G) and centralizes it, contradicting its nonabelianity.
Thus the conjugation action on F*(G) is faithful. Separately, characteristic
prime cores in normal subgroups embed into the ambient prime core.

These general finite-group facts support the central-cover and Sylow-supplement
reductions for Aschbacher–Smith, E.4.3(1), printed p.241 (PDF p.252).
No assertion about the M₁₂ Schur multiplier is made here.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
variable {G : Type*} [Group G] [Finite G]

/-- A simple nonabelian generalized Fitting subgroup has trivial ambient
centralizer. -/
theorem centralizer_eq_bot_of_simple_generalizedFitting
    (L : Subgroup G) [IsSimpleGroup L] [Group.IsPerfect L]
    (hL : generalizedFitting G = L) : centralizer (L : Set G) = ⊥ := by
  let _ : L.Normal := hL ▸ inferInstance
  have hF : fittingSubgroup G = ⊥ := by
    have hFL : fittingSubgroup G ≤ L := hL ▸ fitting_le_generalizedFitting G
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((fittingSubgroup G).subgroupOf L) inferInstance with hb | ht
    · have hh := congrArg (Subgroup.map L.subtype) hb
      simpa only [map_subgroupOf_eq_of_le hFL, Subgroup.map_bot] using hh
    · have hh := congrArg (Subgroup.map L.subtype) ht
      have he : fittingSubgroup G = L := by
        simpa only [map_subgroupOf_eq_of_le hFL, ← MonoidHom.range_eq_map, L.range_subtype] using hh
      have hn : Group.IsNilpotent L := he ▸ inferInstance
      let _ := hn
      exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  have hR : solvableRadical G = ⊥ := by
    let R := solvableRadical G
    have hRF : fittingSubgroupOf R ≤ fittingSubgroup G :=
      le_sSup ⟨fittingSubgroupOf_normal R inferInstance, fittingSubgroupOf_isNilpotent R⟩
    have hb : fittingSubgroup R = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ R.subtype_injective).mp
      exact le_bot_iff.mp (hF ▸ hRF)
    apply Subgroup.card_eq_one.mp
    exact (fitting_eq_bot_iff_card_eq_one_of_solvable R).mp hb
  by_contra hC
  obtain ⟨K, _, hK, _, hc⟩ :=
    exists_commuting_component_of_simple_normal_centralizer_ne_bot L hR
      (Group.IsPerfect.not_isMulCommutative L) hC
  have hKo : IsComponent G K :=
    (isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hR).mp hK
  have hKL : K ≤ L := hL ▸ component_le_generalizedFitting G K hKo
  have hKC : K ≤ centralizer (L : Set G) := by
    rw [commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  exact hK.not_isMulCommutative_of_solvableRadical_eq_bot hR
    (le_centralizer_iff_isMulCommutative.mp (hKC.trans (centralizer_le hKL)))

omit [Finite G] in
/-- Triviality of the ambient prime core descends to a normal subgroup. -/
theorem pCore_eq_bot_of_normal (p : ℕ) [Fact p.Prime]
    (h : pCore p G = ⊥) (L : Subgroup G) [L.Normal] : pCore p L = ⊥ := by
  have hn : ((pCore p L).map L.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore p L).map L.subtype ≤ pCore p G :=
    le_sSup ⟨hn, pCore_isPGroup.map L.subtype⟩
  apply (map_eq_bot_iff_of_injective _ L.subtype_injective).mp
  exact le_bot_iff.mp (h ▸ hl)

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
