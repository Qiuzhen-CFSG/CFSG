module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import CFSG.Quasithin.Chapter7.Section01To05.M23GlobalBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.SourceComplete
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter10.SourceThompsonControl

/-!
# Non-FF reductions under the actual multiple-overgroup hypothesis

The original Thompson subgroup centralizes the full orbit. The standing
guard, obtained from the multiple-overgroup hypothesis, kills its fixed
layer. In the invariant-seed case this constructs the Chapter K hypotheses
for the existing orbit action. The final assembly retains the doubled,
Mathieu, and other irreducible source implications as explicit obligations.

Source: Aschbacher--Smith, 7.0.1--2 and 12.2.2, printed pp.695 and795,
using3.2.2(6),3.1.8 and the full known-simple Theorem A.
-/

public noncomputable section
open Stellmacher Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
private theorem irreducible_restricted_congr {A E : Type*} [Group A]
    [AddCommGroup E] [Module (ZMod 2) E] (ρ : Representation (ZMod 2) A E)
    (X : Subgroup A) {I J : Submodule (ZMod 2) E} (he : I = J)
    (hi : Representation.IsIrreducible
      ((subspaceImageRepresentation ρ J).comp (restrictedSubgroup ρ J X).subtype)) :
    Representation.IsIrreducible
      ((subspaceImageRepresentation ρ I).comp (restrictedSubgroup ρ I X).subtype) := by
  subst I
  exact hi

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The standing guard in the source cubic estimate follows from the actual
multiple-overgroup hypothesis. -/
theorem sourceOrbit_cubic_le_two_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    cubicRatio D.orbitRepresentation ≤ 2 :=
  D.orbit_cubicRatio_le_source h.toHypothesis1221 (Chapter3.hasMaximalOutside_of_many T hmany)

/-- The non-FF branch has no fixed seed vectors, has no fixed orbit vectors,
and places the original Thompson subgroup in the literal two-core of LT.
The source standing guard is derived from the multiple-overgroup premise. -/
theorem sourceOrbit_fixed_and_thompson_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    V ⊓ centralizer (L : Set G) = ⊥ ∧
      fixedSpace D.orbitRepresentation D.orbitComponent = ⊥ ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hJ := Chapter7.NormalizedSource.thompson_centralizes
    D.sourceOrbit_weakClosure_setup (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
  have hFJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (F.moduleSubgroup : Set G) := by
    rwa [D.fundamentalSetup_module h.toHypothesis1221, ← D.sourceOrbit_eq]
  have hc := Chapter10.source_fullModule_fixed_eq_bot_of_many F hmany hFJ
  rw [D.localOrbit_eq] at hc
  have hVU : V ≤ F.fullModule := by
    rw [D.fundamentalSetup_fullModule h.toHypothesis1221]
    exact le_componentOrbit _ _
  have hv : V ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hVU).trans_eq hc)
  refine ⟨hv, D.orbit_fixedSpace_eq_bot hv, ?_⟩
  rw [← D.orbit_centralizer h.toHypothesis1221, ← D.sourceOrbit_eq]
  exact le_inf (sSup_le fun _ hA => hA.1) hJ

/-- The actual M₂₃ code application of 7.5.4. Only the two global numerical
bounds remain; the original action and weak-closure setup are constructed. -/
theorem sourceOrbit_not_m23Code_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hw : ChapterE.globalW D.sourceOrbit T ≤ 2)
    (hr : 6 ≤ ChapterE.globalR D.sourceOrbit) :
    ¬ MathieuCode.IsM23Code (ChapterE.automizerRepresentation D.sourceOrbit) :=
  Chapter7.not_m23Code_of_global_bounds D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hw hr

/-- SQTK for the actual faithful orbit actor, using the full known-simple
catalogue and the original semisimple-section theorem A. -/
theorem sourceOrbit_sqtk
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple D.orbitActor := by
  have hH := h.join_sqtk
  have hL : IsSQTK KnownSimple.IsKnownSimple L := (IsSQTK.equiv (subgroupOfEquivOfLe
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hH.subgroup (L.subgroupOf (L ⊔ (T : Subgroup G))))
  let := D.orbitComponent_quasisimple h
  have hs : ChapterA.Section02.IsSemisimple D.orbitComponent := by
    apply top_unique
    exact le_sSup (show IsComponent D.orbitComponent ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hS := (ChapterA.Section02.theoremA_knownSimple (G := L)).stronglyQuasithin_section
    hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective D.orbitComponentHom
      D.orbitComponentHom_surjective) hs
  exact ⟨ChapterB.QuasisimpleSource.IrreducibleBranch.stronglyQuasithin_of_twoGroup_quotient
    D.orbitComponent D.orbit_quotient_isTwoGroup hS,
    hH.isKGroup.of_surjective D.orbitHom D.orbitHom_surjective⟩

/-- When the original seed equals its orbit, non-FF supplies the missing
fixed-space hypothesis and hence irreducibility of the literal component action. -/
theorem sourceOrbit_irreducible_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) :
    Representation.IsIrreducible (D.orbitRepresentation.comp D.orbitComponent.subtype) := by
  have hc := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have he : D.orbitSpace = D.space := ReducedNormal.subspaceImage_injective
    (L ⊔ (T : Subgroup G)) (hVW.symm.trans D.image_eq.symm)
  exact irreducible_restricted_congr (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G))) he (D.seed_irreducible hc)

/-- All Chapter K source hypotheses on the original orbit and component are
constructed in the invariant-seed branch. No catalogue row is assumed. -/
theorem sourceOrbit_chapterK_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) :
    ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent :=
  ⟨D.sourceOrbit_sqtk h.toHypothesis1221, D.orbit_fitting h.toHypothesis1221,
    D.orbitComponent_quasisimple h.toHypothesis1221, subspaceImageRepresentation_injective _ _,
    D.sourceOrbit_irreducible_of_many h hmany hnon hVW,
    D.sourceOrbit_cubic_le_two_of_many h hmany⟩

/-- Conditional final assembly on the original orbit. The three remaining
source implications are independent obligations; the Chapter K hypotheses
and the exclusion of the concrete J₄ conclusion are discharged here. -/
theorem sourceOrbit_ff_or_orthogonal_of_branches_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : V ≠ D.sourceOrbit →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hother : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      ¬ Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
        Chapter7.NormalizedSource.OrthogonalMinusAlternative
          D.orbitRepresentation D.orbitComponent) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent := by
  classical
  by_cases hff : IsFFModule D.sourceOrbitNormalizerRepresentation
  · exact Or.inl hff
  have hVW : V = D.sourceOrbit := by
    by_contra hne
    exact hdoubled hne hff
  have hK := D.sourceOrbit_chapterK_of_many h hmany hff hVW
  by_cases hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent
  · exact (h.no_J4 (hmathieu hVW hK hm hff)).elim
  · exact Or.inr (hother hVW hK hm hff)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
