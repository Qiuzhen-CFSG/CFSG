module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction

/-!
# Applying the earlier component list to the actual Thompson action

The common Sylow witness and characteristic two construct the elementary
module U_I. The existing Thompson-action theorem verifies all of B.5.3:
faithfulness, trivial two-core, generation by best offenders, finite module,
and a literal SQTK quotient cover. Relative normality of L then makes its
quasisimple star image an ordinary component of that same Thompson image.

Applying the universal earlier component-list implication therefore gives
actual model equivalences for L*, with its original quotient denominator.
The implication is the group-only consequence of B.5.5(1iv)/B.5.6, using
the existing ten-model convention. It remains an explicit earlier-source
input for the chosen class K; it is not proved here or inferred merely
from the class parameter. No local parabolic or recognition conclusion
is assumed by that input.

The model-transport lemma also transports the center and the actual central
quotient in the triple-cover case. No covering group is replaced by its
simple quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3–6,
printed pp.104–105, and the paragraph preceding 15.3.27, p.1130.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open Theory.GroupTheory
universe u

/-- The universal earlier component-list consequence on a genuine B.5.3 action. Its source owner must establish it for K. -/
def ComponentClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type u) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V), FFHypothesis K ρ →
      ∀ C : Subgroup D, IsComponent D C → FFComponentModel C

/-- Transport every model, including the actual center and central quotient of the triple cover. -/
theorem FFComponentModel.of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : FFComponentModel B) : FFComponentModel A := by
  cases h with
  | linearTwo F f => exact .linearTwo F (e.trans f)
  | linearThree F f => exact .linearThree F (e.trans f)
  | symplecticFour F f => exact .symplecticFour F (e.trans f)
  | g2 F f => exact .g2 F (e.trans f)
  | alternatingSix f => exact .alternatingSix (e.trans f)
  | alternatingSeven f => exact .alternatingSeven (e.trans f)
  | tripleSix z q =>
    have hz : (center A).map e.toMonoidHom = center B := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        exact (centerCongr e ⟨a, ha⟩).property
      · intro b hb
        exact ⟨e.symm b, (centerCongr e).symm ⟨b, hb⟩ |>.property, e.apply_symm_apply b⟩
    exact .tripleSix ((centerCongr e).trans z) ((QuotientGroup.congr _ _ e hz).trans q)
  | g2DerivedTwo f => exact .g2DerivedTwo (e.trans f)
  | linearFourTwo f => exact .linearFourTwo (e.trans f)
  | linearFiveTwo f => exact .linearFiveTwo (e.trans f)

variable {G : Type u} [Group G]

/-- The chosen component image lies in the actual Thompson image under the same star map. -/
theorem component_star_le_thompsonStar
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) :
    d.starImage I c.L ≤ d.thompsonStar I :=
  map_mono (comap_mono c.le_thompson)

/-- Relative normality and the given star quasisimplicity give an ordinary component of J(I)*. -/
theorem component_star_isComponent_of_normal
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) :
    IsComponent (d.thompsonStar I) ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) := by
  have hnstar : (d.starImage I c.L).Normal :=
    hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  have hnC : ((d.starImage I c.L).subgroupOf (d.thompsonStar I)).Normal :=
    hnstar.comap (d.thompsonStar I).subtype
  let := c.star_quasisimple
  exact ⟨hnC.isSubnormal, IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (component_star_le_thompsonStar d c)).symm⟩

/-- Apply the earlier universal component list after constructing every B.5.3 hypothesis and the component transport. -/
theorem component_model_of_source [Finite G] {K : GroupClass.{u}}
    (source : ComponentClassificationInput K)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hSQTK : IsSQTK K I) (hf : HasCharacteristicTwo I)
    (hVT : d.V ≤ (d.T : Subgroup G))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hn : (c.L.subgroupOf I).Normal) :
    FFComponentModel (d.starImage I c.L) := by
  have hS : Chapter1.IsSylowIn 2 d.S I := ⟨P, hP⟩
  have hZS := d.Z_le_S hVT
  have hZI := hZS.trans (Chapter1.isSylowIn_iff.mp hS).2.1
  let hU := d.UI_subgroupOf_elementary hS hZS hf
  let := hU
  have hmodels := source (d.thompsonStar I) (Additive ((d.UI I).subgroupOf I))
    (d.thompsonStarAction I hZI)
    (d.thompsonStarFFHypothesis hSQTK hZI hS hZS) _
    (component_star_isComponent_of_normal d c hn)
  exact hmodels.of_equiv (subgroupOfEquivOfLe (component_star_le_thompsonStar d c)).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
