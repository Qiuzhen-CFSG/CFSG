module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceClassificationOuter
/-!
# The B.5 consequence for fully moved non-linear components

The complete B.5.6 alternatives exclude product, hyperplane and outer A₆
cases on a fully moved component. In the remaining quasisimple case, B.5.1
makes the module Irr⁺ unless the actual component is SL₃ or binary SL₄/SL₅.
Restricting to the literal offender subgroup preserves the original seed and
SQTK cover, and Irr⁺ minimality makes that seed the entire module.

This is the classification step used in 11.0.3(5), printed p.760, from
Aschbacher--Smith B.5.1 and B.5.6, printed pp.99--110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.IntersectionClassification
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v
variable {H : Type u} [Group H] [Finite H]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

theorem irrPlus_of_full_component
    (h : FFHypothesis CFSG.KnownSimple.IsKnownSimple ρ) {X : Subgroup H}
    (hX : IsComponent H X) (hm : moved ρ X = ⊤)
    (hnot : ¬ SourceCompletion.NaturalActor X) : IsIrrPlus ρ X ⊤ := by
  let : IsQuasisimple X := hX.2
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX.isCComponent.ne_bot
  let : Nontrivial H := X.subtype_injective.nontrivial
  cases nontrivialAdequateAlternative_knownSimple ρ h with
  | quasisimple hq c =>
    have he : X = generalizedFitting H := hX.eq_of_le
      ⟨(inferInstance : (generalizedFitting H).Normal).isSubnormal, hq⟩
      (component_le_generalizedFitting H X hX)
    subst X
    have hs : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
    cases c.clause_one with
    | irreducible hi _ _ _ _ => exact hs ▸ hi
    | doubleThree F _ e _ _ => exact (hnot (Or.inl ⟨F, ⟨e.groupEquiv⟩⟩)).elim
    | naturalDual d hd _ he =>
      obtain ⟨e⟩ := he
      exact (hnot (Or.inr ⟨d, hd, ⟨e.groupEquiv⟩⟩)).elim
    | repeatedNatural d r hd _ _ _ he =>
      obtain ⟨e⟩ := he
      exact (hnot (Or.inr ⟨d, hd, ⟨e.groupEquiv⟩⟩)).elim
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (Group.IsPerfect.not_isSolvable X inferInstance).elim
  | twoFactors c => exact (not_twoFactors_of_full_component ρ X hX hm c).elim
  | outerSixThree c => exact (not_outerSixThree_of_full_component ρ h hX hm c).elim
  | hyperplane c => exact (not_hyperplane_of_full_component ρ X hm c).elim

theorem source_seed_eq_top {T : Sylow 2 H} {X : Subgroup H}
    {I : Submodule (ZMod 2) W}
    (h : CFSG.Quasithin.ChapterD.Section03.SourceHypotheses CFSG.KnownSimple.IsKnownSimple ρ T X I)
    (hX : IsComponent H X) (hXO : X ≤ offenderSubgroup ρ)
    (hnot : ¬ SourceCompletion.NaturalActor X) : I = ⊤ := by
  let := h.finiteModule
  let := h.normal
  let O := offenderSubgroup ρ
  let σ := ρ.comp O.subtype
  let X₀ := X.subgroupOf O
  have hX₀ : IsComponent O X₀ := hX.subgroupOf hXO
  obtain ⟨c⟩ := h.sqtkQuotient
  have hf : FFHypothesis CFSG.KnownSimple.IsKnownSimple σ :=
    CFSG.Quasithin.ChapterB.InternalThompsonAction.offender_hypothesis ρ
      (c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel))
      (c.equiv.surjective.comp (QuotientGroup.mk'_surjective _))
      c.sqtk h.faithful h.twoCore_eq_bot
  have hm : moved σ X₀ = ⊤ := by
    rw [moved, subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hXO]
    exact h.full_commutator
  have hn : ¬ SourceCompletion.NaturalActor X₀ := by
    intro hc
    exact hnot (SourceCompletion.NaturalActor.of_equiv
      (subgroupOfEquivOfLe hXO).symm hc)
  have hi : IsIrrPlus ρ X ⊤ :=
    (IsIrrPlus.subgroupOf_iff ρ X O hXO ⊤).mp (irrPlus_of_full_component σ hf hX₀ hm hn)
  exact h.seed.eq_of_le ρ hi le_top

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.IntersectionClassification
