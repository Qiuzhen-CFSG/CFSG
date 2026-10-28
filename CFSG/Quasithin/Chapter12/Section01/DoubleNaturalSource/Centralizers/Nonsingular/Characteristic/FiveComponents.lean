module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Residual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# The containing component in the degree-five nonsingular centralizer

The literal point residual has simple quotient L₄(2) by its two-core.
Two-perfection lifts perfectness through that kernel. Its cubic rank is
two, so the proved rank-two seed theorem puts it in a unique normal
C-component of C_G(w). This uses the actual ambient SQTK hypothesis and
does not assume that C_T(w) is Sylow in C_G(w).

Source: Aschbacher--Smith, 12.1.1, printed p.788, using the component-rank
argument of A.3.18. Ordinary-component exclusion and the later normal and
parabolic branches remain with qt-d-double-natural-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
open BinaryNaturalDual.ModelOrbits.AutomorphismModel BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The degree-five point residual lies in a unique normal ambient C-component. -/
theorem doubleNatural_five_nonsingular_containing_cComponent
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      ∃! K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w) ∧
        B.pointResidual w ≤ K ∧ (K.subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let H := B.pointCentralizer w
  let R := (B.pointResidual w).subgroupOf H
  have hRH : B.pointResidual w ≤ H := (B.pointResidual_le w).trans inf_le_right
  let eR := subgroupOfEquivOfLe hRH
  obtain ⟨e₀⟩ := (S.nonsingular_residual_kernel_and_quotient w hw).2
  let e : (R ⧸ pCore 2 R) ≃* LinearGroup 4 :=
    ((QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans e₀).trans
      (projectiveEquivLinear (by decide : 0 < 4))
  let := linear_simple (by decide : 3 ≤ 4)
  let := linear_perfect (by decide : 3 ≤ 4)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := e.isSimpleGroup
  let : Group.IsPerfect (R ⧸ pCore 2 R) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPPerfect 2 R := (B.pointResidual_isPPerfect w).of_surjective
    eR.symm.toMonoidHom eR.symm.surjective
  let : Group.IsPerfect R := hp.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 R)) (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  let : IsQuasisimple (LinearGroup 4) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (linear_center_eq_bot (by decide : 0 < 4))).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv e.symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) pCore_isPGroup hp
  have hr : 2 ≤ primeRank 3 R := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 R) pCore_isPGroup,
      primeRank_equiv 3 ((QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans e₀),
      primeRank_equiv 3 Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hH : IsSQTK KnownSimple.IsKnownSimple H := h.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (D.doubleNatural_point_orderOf_two h B w hw))
  obtain ⟨K,⟨hK,hRK,hKn,_⟩,_⟩ := Section02.simple_core_rank_component_source hH R ht hr
  have hm : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  refine ⟨K.map H.subtype,⟨⟨map_subtype_le _,hm.symm ▸ hK⟩,?_,hm.symm ▸ hKn⟩,?_⟩
  · simpa only [R,map_subgroupOf_eq_of_le hRH] using map_mono (f := H.subtype) hRK
  · intro J hJ
    have hsol : ¬ Group.IsSolvable R := by
      intro hs
      let := hs
      exact ht.not_isSolvable inferInstance
    have he : J.subgroupOf H = K := Section02.IndexTwo.cComponent_unique_over_nonsolvable hsol hJ.1.2 hK
      (comap_mono hJ.2.1) hRK
    simpa only [map_subgroupOf_eq_of_le (show J ≤ H from hJ.1.1)] using
      congrArg (map H.subtype) he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
