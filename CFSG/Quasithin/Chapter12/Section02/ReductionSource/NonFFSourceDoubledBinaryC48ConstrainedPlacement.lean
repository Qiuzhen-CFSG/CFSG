module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedBinaryThree
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.Alternating.OddCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Literal C.4.5 placement for the surviving binary linear stars

For the A8 and SL5(2) star rows, the full core-central marking and the
actual cover theorems remove the center of K/O2(K). Its cubic rank is two
and its outer automorphisms form a two-group. The selected component is
normal, and the ambient cubic rank bound makes its index prime to three.

Any nontrivial image of the original perfect intersection residual retains
its simple SL3(2) quotient through a soluble kernel. In H/K this would
force a factor three, contradicting that index. Thus the original residual
lies in the original K. No parabolic placement or module marking is assumed.

Source: Aschbacher--Smith A.3.18 and C.4.5, printed pp.51--53,152,
applied to the original 12.1.11 witness, p.794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
private instance : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem core_facts_of_linear_star
    {H M LH R W : Subgroup G}
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M LH R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hstar : Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
        alternatingGroup (Fin 8)) ∨
      Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2))) :
    Theory.SpecificGroups.BinaryComponentResidual.Facts (K ⧸ pCore 2 K) := by
  let := hq
  let Q := K ⧸ pCore 2 K
  let hi := hc.constrained_source_input K hK hq hout hfK
  rcases hstar with hs | hs
  · obtain ⟨e⟩ := hs
    let a : coreCentralQuotient K ≃* alternatingGroup (Fin 8) :=
      (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
        (ChapterC.Section04Constrained.source_simple_equiv hi e
          (alternatingGroup.center_eq_bot (by simp)))
    have hzdiv : Nat.card (center Q) ∣ 2 :=
      GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
        8 (by decide) (by decide) (by decide) a
    have hzc : Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 3 := by
      let ek := K.equivMapOfInjective H.subtype H.subtype_injective
      let eq := QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)
      have hh := ChapterC.C27Source.coreQuotient_center_card_from_source hi
      rw [←Nat.card_congr (centerCongr eq).toEquiv] at hh
      exact hh
    have hz : center Q = ⊥ := (eq_bot_iff_card _).mpr (by
      rcases hzc with hzc | hzc
      · exact hzc
      · rw [hzc] at hzdiv
        norm_num at hzdiv)
    let q : Q ≃* coreCentralQuotient K :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
    let e4 := q.trans (a.trans
      (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans (projectiveEquivSL (by decide))))
    exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e4
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inl rfl))
  · obtain ⟨e⟩ := hs
    let a : coreCentralQuotient K ≃* SL(5,ZMod 2) :=
      (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
        (ChapterC.Section04Constrained.source_simple_equiv hi e (binary_center_eq_bot (by decide)))
    let ap := a.trans (projectiveEquivSL (by decide : 0 < 5)).symm
    let e5 := PerfectCentralCovering.centralQuotientEquivOfUniversalKernelEqBot
      Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot ap
    exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv
      (e5.trans (projectiveEquivSL (by decide)))
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

/-- Both surviving binary linear stars force normality of the original K
and literal containment of the original intersection residual in K. -/
theorem sourceOrbit_binary_witness_constrained_linear_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hstar : Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
        alternatingGroup (Fin 8)) ∨
      Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))) :
    K.Normal ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  have hfacts := core_facts_of_linear_star hc K hK hq hout hfK hstar
  let := hq
  let : K.Normal := hc.constrained_component_normal_of_core_threeRank K hK hq hout hfK hfacts.2.1
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    obtain ⟨n,hn⟩ := hfacts.2.2.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hi := cComponent_index_coprime_three_of_quotient K hK hfacts.1 hfacts.2.1
    (hc.sqtk.stronglyQuasithin 3 (by decide) (by decide)) ho
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hqsur : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 LH :=
    (MonoidHom.ker_comp_of_injective _ _ a.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsNilpotent (pCore 2 LH) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqker.symm ▸ inferInstance
  let f : LH →* H ⧸ K := (QuotientGroup.mk' K).comp (inclusion hLH)
  have hf : f = 1 := by
    by_contra hne
    let : Group.IsSolvable f.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient q hqsur f hne
    have hdvd := SimpleSection.card_dvd_of_solvable_representation
      (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) q hqsur f
    rw [Matrix.PSL3Two.card_SL,←index_eq_card] at hdvd
    exact Nat.prime_three.coprime_iff_not_dvd.mp hi ((by decide : 3 ∣ 168).trans hdvd)
  refine ⟨inferInstance,?_⟩
  intro x hx
  let l : LH := ⟨x,hx⟩
  exact (QuotientGroup.eq_one_iff x).mp (DFunLike.congr_fun hf l)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
