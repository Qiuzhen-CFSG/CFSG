module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixC28
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingLinearFive
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.Alternating.OddCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Literal residual placement in the A₆ constrained A₈ branch

The actual star is A₈ by the existing alternating source exclusions. The
covering center of K/O₂(K) divides two and has order one or three, hence is
trivial. The binary linear-four cubic-rank and outer-automorphism facts make
the index of the normal component prime to three. A nontrivial image of the
original perfect intersection residual would retain its simple A₆ section
through a soluble kernel, forcing a factor three. Thus that same residual
lies in K.

Source: Aschbacher--Smith A.3.18, C.2.7 and C.4.5, printed pp.51--53,146,152,
applied to the actual A₆ row of 7.3.4, p.699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem core_facts_of_eight_star
    {H M LH R W : Subgroup G}
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M LH R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin 8)) :
    Theory.SpecificGroups.BinaryComponentResidual.Facts (K ⧸ pCore 2 K) := by
  let := hq
  let Q := K ⧸ pCore 2 K
  let hi := hc.constrained_source_input K hK hq hout hfK
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

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

/-- The original A₆ intersection residual lies in the selected constrained
component. Its A₈ star marking and normality are derived from the same witness. -/
theorem sourceOrbit_six_witness_constrained_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv
      (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨hKn,⟨a8⟩⟩ := D.sourceOrbit_six_witness_constrained_eight h hmodel hw K hK hq hout hfK
  let : K.Normal := hKn
  have hspan := hc.normalized_span_eq hn
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  have hfacts := core_facts_of_eight_star hc K hK hq hout hfK a8
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    obtain ⟨n,hn⟩ := hfacts.2.2.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hi := cComponent_index_coprime_three_of_quotient K hK hfacts.1 hfacts.2.1
    (hc.sqtk.stronglyQuasithin 3 (by decide) (by decide)) ho
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by norm_num : 4 ≤ Nat.card (Fin 6)))).trans QuotientGroup.quotientBot))
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨c,_⟩,_⟩
  let r : LH →* (L ⧸ pCore 2 L) := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hrk : r.ker = pCore 2 LH := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 LH) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable r.ker := hrk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 LH))
  let π : LH →* alternatingGroup (Fin 6) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp r)
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsSolvable π.ker := by
    have he : π.ker = (center (L ⧸ pCore 2 L)).comap r := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
        ← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rw [he]
    exact isSolvable_comap_of_solvable_ker r _
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  let f : LH →* H ⧸ K := (QuotientGroup.mk' K).comp (inclusion hLH)
  have hf : f = 1 := by
    by_contra hne
    let : Group.IsSolvable f.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient π hπ f hne
    have hdvd := SimpleSection.card_dvd_of_solvable_representation
      (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))) π hπ f
    have hthree : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [←index_eq_card] at hdvd
    exact Nat.prime_three.coprime_iff_not_dvd.mp hi (hthree.trans hdvd)
  refine ⟨hKn,?_⟩
  intro x hx
  let l : LH := ⟨x,hx⟩
  exact (QuotientGroup.eq_one_iff x).mp (DFunLike.congr_fun hf l)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
