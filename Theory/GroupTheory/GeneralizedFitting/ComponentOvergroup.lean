module
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
/-!
# Ordinary components of an overgroup of the generalized Fitting subgroup

An ordinary component B of M containing F*(G) is an ambient component.
Otherwise B centralizes the ambient Fitting subgroup and every ambient
component, by ordinary component calculus inside M. Generalized-Fitting
self-centralization then makes B solvable, a contradiction.

The statement concerns ordinary components; no upward promotion for general
C-components or arbitrary local subgroups is asserted.
Source: standard component calculus, used in Aschbacher–Smith C.2.13, p.148.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- A component in an overgroup of F*(G) is already an ambient component. -/
theorem IsComponent.of_generalizedFitting_overgroup {B M : Subgroup G}
    (hBM : B ≤ M) (hB : IsComponent M (B.subgroupOf M))
    (hFM : generalizedFitting G ≤ M) : IsComponent G B := by
  by_contra hnot
  have hBF : B ≤ centralizer (fittingSubgroup G : Set G) := by
    have hfM : fittingSubgroup G ≤ M := (fitting_le_generalizedFitting G).trans hFM
    let : Group.IsSolvable ((fittingSubgroup G).subgroupOf M) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hfM).toMonoidHom) (subgroupOfEquivOfLe hfM).injective
    have hc := hB.le_centralizer_of_solvable_normal ((fittingSubgroup G).subgroupOf M)
    intro b hb f hf
    exact congrArg Subtype.val (hc (show (⟨b,hBM hb⟩ : M) ∈ B.subgroupOf M from hb)
      ⟨f,hfM hf⟩ hf)
  have hBE : B ≤ centralizer (componentLayer G : Set G) := by
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro K hK
    have hKM : K ≤ M := (component_le_generalizedFitting G K hK).trans hFM
    have hne : K.subgroupOf M ≠ B.subgroupOf M := by
      intro he
      have hk : K = B := by
        have hh := congrArg (map M.subtype) he
        rwa [map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hBM] at hh
      exact hnot (hk ▸ hK)
    have hc := (hK.subgroupOf hKM).commutator_eq_bot_of_ne hB hne
    have hh := congrArg (map M.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hBM,Subgroup.map_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hBGF : B ≤ centralizer (generalizedFitting G : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hBF) (le_centralizer_iff.mp hBE)
  have hBfit : B ≤ fittingSubgroup G := hBGF.trans centralizer_generalizedFitting_le_fitting
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hBfit) (inclusion_injective hBfit)
  let : Group.IsSolvable (B.subgroupOf M) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hBM).toMonoidHom) (subgroupOfEquivOfLe hBM).injective
  exact hB.isCComponent.not_isSolvable inferInstance
end Theory.GroupTheory
