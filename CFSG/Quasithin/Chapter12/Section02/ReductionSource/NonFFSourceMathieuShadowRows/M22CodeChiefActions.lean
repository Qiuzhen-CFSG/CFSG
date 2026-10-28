module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeCubicChiefs
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic.Source
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Natural
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs

/-!
# Actual chief actions in the exceptional original M22-code parabolic

The full automizer marking gives the minimum-rank condition of 3.1.9(6)
and exactly three noncentral factors for each actual cubic actor. Restriction
to the original normalizer retains its entire relative-centralizer kernel:
a cubic either centralizes the original orbit or acts with that same count.
The original H-overlap normalization is supplied by the qrc source geometry.

Under the temporary inside-core assumption the same H-span is elementary.
We construct a minimal maximum elementary actor, quadratic on that span,
and obtain the original two-chief-factor rank/centralizer equalities and
natural chief-action alternatives. No chief-action classification, actor,
normalization, or ratio premise is added to the original inputs.

The exceptional parabolic quotient and the contradiction to inside-core
containment remain to be proved; the full-orbit selection does not follow
from this increment alone.
Source: Aschbacher--Smith 3.1.9(1--6), 8.2.2(1), printed pp.576--578,714--715.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The minimum-rank condition of 3.1.9(6) on the full original automizer. -/
theorem sourceOrbit_m22_code_small_actor_rank
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A)
    (hr : actionRatio (automizerRepresentation D.sourceOrbit) A ≤ 2) :
    2 ≤ rank A := by
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h d
  exact Chapter8.Section02.Offenders.Parabolic.Exclusion.code_actor_rank_of_equivariant
    _ a ha (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) hE A hA hr

/-- Cubics in the full faithful automizer have three noncentral factors
on the same original orbit and on its dual. -/
theorem sourceOrbit_m22_code_cubic_chiefs
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : Nat.card A = 3) :
    HasCount ((automizerRepresentation D.sourceOrbit).comp A.subtype) 3 ∧
      HasCount (Representation.dual ((automizerRepresentation D.sourceOrbit).comp A.subtype)) 3 := by
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h d
  exact Chapter8.MathieuShadowRows.marked_m22_code_cubic_chiefs
    ((automizerRepresentation D.sourceOrbit).comp A.subtype) (a.comp A.subtype) (ha.comp A.subtype_injective)
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
    (fun x v => hE x.val v) hA

/-- Retain the full original kernel: a cubic normalizing the orbit either
centralizes it or has exactly three noncentral factors, also on the dual.
The moving alternative is detected on the original group, not by assuming
that its entire normalizer has two-group centralizer. -/
theorem sourceOrbit_m22_code_cubic_chiefs_or_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hA : Nat.card A = 3) :
    A ≤ centralizer (D.sourceOrbit : Set G) ∨
      (HasCount (sourceRepresentation A D.sourceOrbit hAN) 3 ∧
        HasCount (sourceRepresentation A D.sourceOrbit hAN).dual 3) := by
  by_cases hC : A ≤ centralizer (D.sourceOrbit : Set G)
  · exact Or.inl hC
  right
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h d
  let f := (a.comp D.sourceOrbit.normalizerMonoidHom.rangeRestrict).comp (inclusion hAN)
  have hk : f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf A := by
    rw [← MonoidHom.comap_ker, D.sourceOrbit_m22_full_marking_kernel a ha]
    rfl
  let : Fact (Nat.card A).Prime := ⟨by rw [hA]; decide⟩
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with hb | ht
    · exact hb
    · apply (hC ?_).elim
      intro x hx
      have hh : (⟨x,hx⟩ : A) ∈ f.ker := ht.symm ▸ mem_top _
      rw [hk] at hh
      exact hh
  apply Chapter8.MathieuShadowRows.marked_m22_code_cubic_chiefs _ f hf
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) _ hA
  intro x v
  exact hE (D.sourceOrbit.normalizerMonoidHom.rangeRestrict (inclusion hAN x)) v

/-- In the temporary inside-core branch the original overlap normalizes V,
so the same cubic count applies there without an added normalizer premise. -/
theorem sourceOrbit_m22_code_inside_core_overlap_cubics
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    ∃ hNM : H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G),
      ∀ (A : Subgroup G) (hAH : A ≤ H ⊓ normalizer (L : Set G)), Nat.card A = 3 →
        A ≤ centralizer (D.sourceOrbit : Set G) ∨
          (HasCount (sourceRepresentation A D.sourceOrbit (hAH.trans hNM)) 3 ∧
            HasCount (sourceRepresentation A D.sourceOrbit (hAH.trans hNM)).dual 3) := by
  obtain ⟨_,hNM,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  exact ⟨hNM,fun A hAH hA =>
    D.sourceOrbit_m22_code_cubic_chiefs_or_centralizes h.toHypothesis1221 d A (hAH.trans hNM) hA⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original exceptional span is elementary, with one minimal maximum
actor quadratic on the span and sharp on every noncentral chief factor. -/
theorem sourceOrbit_m22_code_inside_core_chief_actions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
        ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
        (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
        (∀ s : SeriesOn U,
          s.noncentralCount = 2 ∧
          2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A ∧
          fixedCodim (normalRepresentation U) A =
            2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) ∧
          U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) ∧
          ∀ i, ¬ s.Central i →
            Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
        ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
          ChapterB.ChiefNaturalAlternatives
            (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
          subspaceCommutator (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ⊤
            (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) = ⊤ := by
  obtain ⟨c,_,hq,hd⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hM,hu⟩ := D.original_uniqueness h
  let q := c.toQRCConfiguration (c.no_common_normal hu)
  let := source_elementary_span_of_notFF q hcore (source_notFF_of_ratio_two q hq)
  let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
  let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core q hcore).trans (twoCore_le H))
  let := hU
  have hJ := D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hne := D.sourceOrbit_weakClosure_setup.nontrivial
  obtain ⟨A,hA,hAR,hquad,hmin,heq⟩ := c.sqtk_minimal_actor_equalities
    h.simpleQTKE hM hu hJ hne hcore hd hq
  refine ⟨hU,A,hA,hAR,hquad,hmin,?_,?_⟩
  · intro s
    have he := heq s
    exact ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1⟩
  · exact c.sqtk_chief_natural_alternatives h.simpleQTKE hM hu hJ hne hcore hd hq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
