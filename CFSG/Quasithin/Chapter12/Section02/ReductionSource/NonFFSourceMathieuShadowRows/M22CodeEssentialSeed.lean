module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeNonsolvableAlignment
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialChiefActor
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs

/-!
# The original essential quotient and sharp actor in the nonsolvable M22-code branch

Under the temporary inside-core assumption, the original qrc construction
selects an essential quotient of the actual H-span. The same maximum elementary
subgroup from the two-chief-factor argument is a sharp offender of rank at
least two on its faithful action. Its original lift centralizes V, and hence
fixes the entire image of V in this quotient. The quotient action and every
noncentral chief action have equivariant image identifications preserving the
original maps. The same offender also prevents mixing small natural actions
with higher-field linear actions between those factors.

The essential quotient is constructed here; none of its seed or actor
properties is assumed. The Cartan, cubic-count and symmetric-five exclusions
in 3.1.9(6), and the contradiction to inside-core containment, remain to be
proved before the original M22-code exclusion can be concluded.
Source: Aschbacher--Smith, 3.1.9(6), printed pp.577--578, applied in
8.2.2(1), printed p.715 (PDF pp.594--595,732), refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement
open Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_m22_code_inside_core_nonsolvable_seed
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
      ∃ a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
          (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)),
        ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
          (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
            ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
          EssentialChiefActor a A := by
  obtain ⟨hU,A,hA,hAR,hquad,hr,hmin,hchief⟩ :=
    D.sourceOrbit_m22_code_inside_core_large_chief_actor h hmany hV hnon d hH hcore
  let := hU
  obtain ⟨c,_,hq,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨_,hu⟩ := D.original_uniqueness h
  obtain ⟨a⟩ := c.sqtk_essential_seed_action hu D.sourceOrbit_weakClosure_setup.nontrivial hcore hq
  have hsharp := a.sharp_offender_of_chiefs A (fun s i hi =>
    ⟨(hchief s i hi).1, (hchief s i hi).2.1⟩)
  have hD := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  let := a.irreducible
  have hker (s : SeriesOn ((conjugateSpan H D.sourceOrbit).subgroupOf H))
      (i : Fin s.series.length) (hi : ¬ s.Central i) :
      a.representation.ker = (s.factorRepresentation i).ker := by
    let := s.factorRepresentation_irreducible i
    exact (a.kernel_eq_core hD hns ⟨_,hsharp.1⟩).trans
      (ChapterB.minimalParabolic_nonsolvable_chief_kernel (s.factorRepresentation i)
        hD _ a.original_minimal hns ⟨_,(hchief s i hi).1⟩).symm
  have hlarge : 2 ≤ rank (A.map a.projection) := by
    obtain ⟨s⟩ := SeriesOn.exists_series ((conjugateSpan H D.sourceOrbit).subgroupOf H)
    have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
      by_contra! hz
      have hz' := s.noncentralCount_eq_zero_iff.mpr hz
      have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
      omega
    obtain ⟨i,hi⟩ := hex
    have he : rank (A.map a.projection) = rank (actionSubgroup (s.factorRepresentation i) A) := by
      change rank (actionSubgroup a.representation A) = _
      rw [rank_actionSubgroup_eq_log_relIndex,rank_actionSubgroup_eq_log_relIndex,hker s i hi]
    rw [he,(hchief s i hi).2.2]
    exact hr
  have hAC : A.map H.subtype ≤ centralizer (D.sourceOrbit : Set G) := by
    have hAJ : A ≤ elementaryAbelianMaxJ ((T.subtype hH.1.1.2) : Subgroup H) := le_sSup hA
    have he : (elementaryAbelianMaxJ ((T.subtype hH.1.1.2) : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hm := map_mono (f := H.subtype) hAJ
    rw [he] at hm
    exact hm.trans (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hfix : Chapter3.quotientSeed H D.sourceOrbit a.kernel ≤
      fixedSpace a.kernel.quotientRepresentation A := by
    intro w hw x
    exact Chapter3.quotientSeed_fixed_by_centralizer H D.sourceOrbit a.kernel x.val
      (hAC (mem_map_of_mem H.subtype x.property)) w hw
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,
    ⟨hsharp.1,hlarge,hsharp.2,hAC,hfix,?_,?_,?_⟩⟩
  · intro s i hi
    refine ⟨(hchief s i hi).1,?_⟩
    apply chief_equiv_of_kernel_eq
    simpa only [actionHom_ker_eq] using hker s i hi
  · exact fun s i hi => (hchief s i hi).2.1
  · exact essential_small_iff_chief_small a hD hns A
      (fun s i hi => ⟨(hchief s i hi).1,(hchief s i hi).2.1⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
