module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceInput
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.Products

/-!
# Fully moved components in the ordinary B.5 alternatives

A component in an internal product lies in one of its factors. If that
component moves the whole module, its prescribed quotient summand is the
whole fixed quotient. The opposite summand is zero, contradicting its
faithful nontrivial factor action. Full movement also excludes the
hyperplane alternative. In the quasisimple Fitting case the component
equals the generalized Fitting subgroup, and B.5.1(2) gives Irr⁺.

The outer A₆–C₃ case is handled separately using the original B.5.7
construction, without the disputed fixed-space splitting.
Source: Aschbacher--Smith, D.3.20, p.204, and B.5.1, B.5.6, pp.99--105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u v
variable {H : Type u} [Group H]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W) (X : Subgroup H)

private theorem moved_mono {A B : Subgroup H} (h : A ≤ B) :
    moved ρ A ≤ moved ρ B :=
  Submodule.span_mono (by rintro _ ⟨g, hg, v, hv, rfl⟩; exact ⟨g, h hg, v, hv, rfl⟩)

private theorem component_le_factor {A B : Subgroup H}
    (p : InternalProduct A B) (hX : IsComponent H X) : X ≤ A ∨ X ≤ B := by
  let := p.swap.second_normal
  let := p.second_normal
  rcases hX.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hX.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : X ≤ centralizer ((A ⊔ B : Subgroup H) : Set H) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [p.sup_eq_top] at hc
  have he : ⁅X, X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (X : Set H) ⊆ (⊤ : Subgroup H) from Set.subset_univ _)))
  let := hX.2
  rw [commutator_eq_self] at he
  exact (hX.isCComponent.ne_bot he).elim

private theorem no_first_factor (c : SourceTwoFactorCase ρ)
    (hm : moved ρ X = ⊤) (hX : X ≤ c.first) : False := by
  have hs : c.firstSpace.toSubmodule = ⊤ := top_unique (hm ▸
    (moved_mono ρ hX).trans
      (ChapterB.SourceB513.factor_moved_le c.firstCase))
  have hq : ((fixed ρ).quotientImage c.firstSpace).toSubmodule = ⊤ := by
    change c.firstSpace.toSubmodule.map ρ.invariants.mkQ = ⊤
    rw [hs, Submodule.map_top, LinearMap.range_eq_top.mpr ρ.invariants.mkQ_surjective]
  have hz : ((fixed ρ).quotientImage c.secondSpace).toSubmodule = ⊥ := by
    simpa only [hq, top_inf_eq] using (disjoint_iff.mp c.decomposition.disjoint)
  let : Subsingleton ((fixed ρ).quotientImage c.secondSpace).toSubmodule := by
    rw [hz]
    infer_instance
  let : Nontrivial c.second := c.secondCase.nontrivial
  apply not_subsingleton c.second
  exact ⟨fun a b => c.secondCase.faithful (Subsingleton.elim _ _)⟩

/-- Full movement by one actual component excludes the two-factor module case. -/
theorem not_twoFactors_of_full_component (hX : IsComponent H X)
    (hm : moved ρ X = ⊤) (c : SourceTwoFactorCase ρ) : False := by
  rcases component_le_factor X c.product hX with ha | hb
  · exact no_first_factor ρ X c hm ha
  · exact no_first_factor ρ X
      { first := c.second, second := c.first, product := c.product.swap
        firstSpace := c.secondSpace, secondSpace := c.firstSpace
        decomposition := c.decomposition.symm
        firstCase := c.secondCase, secondCase := c.firstCase } hm hb

/-- Full movement is incompatible with the source's codimension-one supplement. -/
theorem not_hyperplane_of_full_component
    (hm : moved ρ X = ⊤) (c : HyperplaneCase ρ) : False := by
  have ht : moved ρ ⊤ = ⊤ := top_unique (hm ▸ moved_mono ρ le_top)
  have he := c.hyperplane
  rw [ht, top_sup_eq] at he
  rw [Module.finrank_zero_of_subsingleton] at he
  omega

/-- B.5.1(2) on the original component, identified with F*(H). -/
theorem irrPlus_of_quasisimple_fitting (hX : IsComponent H X)
    (hm : moved ρ X = ⊤) (hc : fixedSpace ρ X ≠ ⊥)
    (hq : IsQuasisimple (generalizedFitting H))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting H)) :
    IsIrrPlus ρ X ⊤ := by
  have he : X = generalizedFitting H := hX.eq_of_le
    ⟨(inferInstance : (generalizedFitting H).Normal).isSubnormal, hq⟩
    (component_le_generalizedFitting H X hX)
  subst X
  have hs : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ (generalizedFitting H)) := by
    intro hh
    apply hc
    simpa only [hs, top_inf_eq] using (disjoint_iff.mp hh.disjoint)
  simpa only [hs] using (c.clause_two hn).1

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
