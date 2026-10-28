module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeEssentialSeed
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.SpanImageReduction

/-!
# The original M22-code whole-span action modulo its two-core

In the nonsolvable inside-core branch, retain the constructed essential
quotient and the same minimum sharp actor of rank at least two. The original
H-span has two noncentral chief factors; choosing one and applying their
literal action alignment identifies the faithful action on the whole span
modulo its two-core with that same essential actor. The equivalence preserves
every original element and subgroup image, including the source Sylow and
the selected sharp actor. The whole-span image of the essential-action
kernel is exactly that two-core.

All seed, actor, and common-kernel premises are discharged from the original
inputs. The temporary inside-core and nonsolvable branch hypotheses remain.
The Cartan, cubic-count, and symmetric-five exclusions of 3.1.9(6) are still
needed before eliminating this branch or selecting the original M24 cocode.
Source: Aschbacher--Smith, 3.1.9(6), pp.577--578, applied in 8.2.2(1), p.715.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Theory.GroupTheory
open Chapter8.MathieuShadowRows
open Representation Representation.BinaryOffender Subgroup Stellmacher
open scoped IsMulCommutative ENNReal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original nonsolvable M22-code branch constructs its essential
actor as the whole-span image modulo its two-core, preserving the same
sharp actor, source seed, and every original action map. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_span_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      let ρ := normalRepresentation U
      ∃ a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
          (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)),
        ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ A ≤ pCore 2 H ∧ IsQuadratic ρ A ∧
          (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
            ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
          EssentialChiefActor a A ∧
          Nonempty (MathieuCode.NormalizedShadowRows.ActionImageReduction ρ a.representation) := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_seed h hmany hV hnon d hH hcore hns
  let := hU
  let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  exact ⟨hU,a,A,hA,hAR,hquad,hmin,ha,essential_span_image_reduction a A ha s i hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
