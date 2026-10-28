module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.SourceTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Generated

/-!
# The generalized Fitting subgroup of the actual Thompson image

Relative normality of L and I = LS give a two-group quotient I*/L*.
Restriction gives the same quotient property for J(I)*/L*. The selected
star subgroup is already an ordinary component of J(I)*, and the latter
has trivial two-core. The quasisimple two-quotient theorem therefore
identifies F*(J(I)*) with the literal L* inside it.

This is the group input to excluding the nonquasisimple B.5.6 cases.
It neither assumes nor proves simplicity of L/O₂(L). The complete
classification implication still has to be applied to the faithful
Thompson action with its genuine SQTK cover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3–6,
printed pp.104–105, and 15.3.26–27, pp.1130–1131.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open EightGeometry.NaturalModule.Recognition
open Parabolics.Placement.ModelComparison
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_subgroup_two {D : Type*} [Group D]
    (L J : Subgroup D) [L.Normal] (h : IsPGroup 2 (D ⧸ L)) :
    IsPGroup 2 (J ⧸ L.subgroupOf J) := by
  let f := (QuotientGroup.mk' L).comp J.subtype
  have hk : f.ker = L.subgroupOf J := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  let e := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact h.of_injective ((QuotientGroup.kerLift f).comp e.toMonoidHom)
    ((QuotientGroup.kerLift_injective f).comp e.injective)

omit [Finite G] in
/-- The selected component has two-group quotient in the whole star actor. -/
theorem star_component_two_quotient (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    let := starComponent_normal d c hn
    IsPGroup 2 (d.Star I ⧸ d.starImage I c.L) := by
  let := starComponent_normal d c hn
  have hS : IsPGroup 2 (d.S.subgroupOf I) := by
    have he : d.S.subgroupOf I = (P : Subgroup I) := by
      rw [← hP]
      exact comap_map_eq_self_of_injective I.subtype_injective _
    rw [he]
    exact P.isPGroup'
  exact isPGroup_quotient_of_sup_eq_top _ _ (hS.map (d.starMap I))
    (star_component_sup_sylow d c hI)

/-- The generalized Fitting subgroup of the classified Thompson image is
exactly the selected component, with its original inclusion. -/
theorem thompson_fitting_eq_component (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hZS : d.Z ≤ d.S) :
    generalizedFitting (d.thompsonStar I) =
      (d.starImage I c.L).subgroupOf (d.thompsonStar I) := by
  let := starComponent_normal d c hn
  let := (component_star_isComponent d c).2
  apply generalizedFitting_eq_of_quasisimple_two_quotient
  · exact quotient_subgroup_two _ _ (star_component_two_quotient d c hn hI P hP)
  · exact d.thompsonStar_twoCore_eq_bot ⟨P, hP⟩ hZS

/-- Quasisimplicity here is inherited from the genuine component witness;
it is not simplicity of the core quotient. -/
theorem thompson_fitting_quasisimple (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hZS : d.Z ≤ d.S) : IsQuasisimple (generalizedFitting (d.thompsonStar I)) := by
  rw [thompson_fitting_eq_component d c hn hI P hP hZS]
  exact (component_star_isComponent d c).2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
