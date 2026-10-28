module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedLocals
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedRankOne
public import Theory.GroupTheory.PerfectSimpleOrderNormalizer

/-!
# The binary linear-three constrained endpoint

If the constrained star component is SL₃(2), its full core-central quotient
is the same simple group as the original intersection residual's two-core
quotient. The residual's nontrivial core-central action is perfect and inner.
Its inner lift has image order divisible by 168 and hence fills the component
quotient. It cannot normalize the nontrivial two-group induced by the original
radical, since an automorphism overgroup containing all inner automorphisms
has trivial two-core.

All quotient, action and radical maps are constructed from the original
reciprocal witness. Degree-one field transport is explicit; the argument
allows outer radical automorphisms and requires no parabolic placement.
Source: Aschbacher--Smith C.4.3--5 and 12.1.11, printed pp.152,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual constrained star cannot be linear-three over a degree-one
binary field. The comparison with the original quotient is constructed. -/
theorem sourceOrbit_binary_witness_constrained_not_binary_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (E : BinaryField) (hE : E.degree = 1) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      SL(3,E.Carrier)) := by
  rintro ⟨e⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,_,_,_,_,_,eLH,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let e₂ := e.trans (ExtensionConsequences.degreeOneNaturalEquiv E hE 3).groupEquiv
  let eQ : Q ≃* BinaryLinearThree.Group :=
    (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (ChapterC.Section04Constrained.source_simple_equiv
        (hc.constrained_source_input K hK hq hout hfK) e₂
        Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot)
  let q := (eLH.trans eQ.symm).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hqsur : Function.Surjective q :=
    (eLH.trans eQ.symm).surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 LH :=
    (MonoidHom.ker_comp_of_injective _ _ (eLH.trans eQ.symm).injective).trans
      (QuotientGroup.ker_mk' _)
  let : Group.IsNilpotent (pCore 2 LH) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqker.symm ▸ inferInstance
  have hspan := hc.normalized_span_eq hn
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let X := LH.subgroupOf H
  let B := coreCentralActorImage K X
  let Y := coreCentralActorImage K (R.subgroupOf H)
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hXK : X ≤ normalizer (K : Set H) := by
    simpa only [hspan] using hc.constrained_span_normalizes_intrinsic K hK hq
  let eX : LH ≃* X.subgroupOf (normalizer (K : Set H)) :=
    (subgroupOfEquivOfLe hLH).symm.trans (subgroupOfEquivOfLe hXK).symm
  let b : LH →* B := ((normalizerCoreCentralAction K).subgroupMap
    (X.subgroupOf (normalizer (K : Set H)))).comp eX.toMonoidHom
  have hb : Function.Surjective b :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp eX.surjective
  let a := B.subtype.comp b
  have har : a.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hb,←MonoidHom.range_eq_map,
      range_subtype]
  have hane : a ≠ 1 := by
    intro he
    apply hc.constrained_span_action_nontrivial K hK hq hout
    rw [hspan]
    change B = ⊥
    rw [←har,he,MonoidHom.range_one]
  have hXR : X ≤ normalizer (R.subgroupOf H : Set H) := by
    intro x hx r
    exact hc.span_normalizes_radical (hspan.symm ▸ hx) (r : G)
  have hY : IsPGroup 2 Y := hc.isRadical.isPGroup.comap_subtype.map _
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp ht)).elim
  let : Group.IsSolvable (MulAut.Outer Q) := hc.constrained_core_central_outer_solvable K hq
  apply hc.constrained_radical_action_nontrivial K hK hq hout hfK
  exact MulAut.perfect_simple_quotient_normalizer_p_eq_bot hz q hqsur a hane Y hY
    (har ▸ coreCentralActorImage_normalizes K X (R.subgroupOf H) hXR)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
