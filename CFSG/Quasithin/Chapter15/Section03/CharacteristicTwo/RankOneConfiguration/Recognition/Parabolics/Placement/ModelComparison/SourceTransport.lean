module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The actual component inside the classified Thompson action

A C-component of J(I) remains a C-component inside I. Its star image is
subnormal, and the given quasisimplicity makes its restriction to J(I)*
an ordinary component. All comparisons use the actual subgroup inclusions.

The characteristic-two and Sylow inputs construct the elementary internal
module. ThompsonAction then supplies the faithful offender-generated action
and genuine SQTK cover needed for B.5.3. SQTK is retained explicitly; it
does not follow from LocalData alone. No component model is assumed here.

Source: Aschbacher–Smith, 1 March 2004, A.3.3(2), printed p.42;
B.2.5–7, p.76; B.5.3, p.104; 15.3.26, p.1130.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G]

/-- The same source C-component, now internal to I. -/
theorem component_isCComponent_in (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : (c.L.subgroupOf I).IsCComponent :=
  LocalData.thompson_component_in c.le_thompson c.component

/-- The star component belongs to the literal Thompson image. -/
theorem component_star_le_thompson (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : d.starImage I c.L ≤ d.thompsonStar I :=
  map_mono (comap_mono c.le_thompson)

/-- The selected star component is an ordinary component of J(I)*. -/
theorem component_star_isComponent (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) :
    IsComponent (d.thompsonStar I) ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) := by
  have hs : (d.starImage I c.L).IsSubnormal :=
    (component_isCComponent_in d c).subnormal.map (QuotientGroup.mk'_surjective _)
  let := c.star_quasisimple
  exact ⟨hs.subgroupOf, IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (component_star_le_thompson d c)).symm⟩

/-- Construct all B.5.3 hypotheses and the selected ordinary component on
the same faithful Thompson action. The SQTK hypothesis is explicit. -/
theorem thompson_source_inputs [Finite G] (d : LocalData G) {I : Subgroup G}
    {K : GroupClass.{u}} (hSQTK : IsSQTK K I)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hS : CFSG.Quasithin.Chapter1.IsSylowIn 2 d.S I)
    (hf : Chapter15.Section03.CharacteristicTwo.HasCharacteristicTwo I) (c : ComponentWitness d I) :
    ∃ (hZI : d.Z ≤ I) (hU : IsElementaryAbelian 2 ((d.UI I).subgroupOf I)),
      let := hU
      FFHypothesis K (d.thompsonStarAction I hZI) ∧
        IsComponent (d.thompsonStar I)
          ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) := by
  have hZS := d.Z_le_S hVT
  have hZI := hZS.trans (CFSG.Quasithin.Chapter1.isSylowIn_iff.mp hS).2.1
  let hU := d.UI_subgroupOf_elementary hS hZS hf
  let := hU
  exact ⟨hZI, hU, d.thompsonStarFFHypothesis hSQTK hZI hS hZS,
    component_star_isComponent d c⟩

/-- The explicit carrier comparison for the component in the Thompson image. -/
noncomputable def componentThompsonEquiv (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) :
    (d.starImage I c.L).subgroupOf (d.thompsonStar I) ≃* d.starImage I c.L :=
  subgroupOfEquivOfLe (component_star_le_thompson d c)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
