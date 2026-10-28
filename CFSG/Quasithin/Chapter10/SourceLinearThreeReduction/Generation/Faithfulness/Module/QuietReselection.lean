module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuietFixedSeed
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence

/-!
# Reselecting the original setup inside the fixed-seed orbit

A noncentral invariant subspace of the literal R₂(L₀T) supplies an Irr⁺
constituent. Source3.2.3 reselects its homogeneous seed inside the same
T-invariant orbit. The new local module lies in the fixed-seed orbit,
and its full M-orbit lies in the original V_M. Minimal full-module order
therefore preserves V_M exactly, together with G,T,L,L₀ and M.

The conclusion concerns fixation of the reselected local module. It does
not turn that fixation into fixation of its larger full M-orbit.
Source: Aschbacher--Smith3.2.3,4.4.14 and10.2.3(2), printed pp.580,
624--625 and745 (combined manuscript of1 March2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source3.2.3 chooses an actual setup whose local module lies in the fixed-seed orbit. -/
theorem sourceQuietFixedSpan_reselection
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.moduleSubgroup ≤ sourceQuietFixedSpan D ∧ E.fullModule ≤ D.fullModule := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let U := (sourceQuietFixedSpan D).subgroupOf H
  have hUH : sourceQuietFixedSpan D ≤ H :=
    (sourceQuietFixedSpan_le D).trans (D.fullModule_le_orbit.trans le_sup_left)
  have hred : IsPReduced 2 U := sourceQuietFixedSpan_reduced D
  let := hred.normal
  let J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup H)) :=
    AddSubgroup.toZModSubmodule 2 ((U.subgroupOf (ReducedNormal.ModuleGroup H)).toAddSubgroup)
  have hJX : X ≤ subspaceStabilizer (ReducedNormal.representation H) J := by
    apply le_subspaceStabilizer
    intro x hx v hv
    exact (inferInstance : U.Normal).conj_mem v.toMul.val hv x
  have hn : ¬ J ≤ fixedSpace (ReducedNormal.representation H) X := by
    intro hf
    have hc : sourceQuietFixedSpan D ≤ centralizer (localOrbit T L : Set G) := by
      intro v hv x hx
      let vH : H := ⟨v,hUH hv⟩
      let vR : ReducedNormal.ModuleGroup H := ⟨vH,hred.le_reducedPSubgroup hv⟩
      have he := congrArg (fun w : Additive (ReducedNormal.ModuleGroup H) => w.toMul.val.val)
        (hf (show Additive.ofMul vR ∈ J from hv)
          ⟨⟨x,(show localOrbit T L ≤ H from le_sup_left) hx⟩,hx⟩)
      change x * v * x⁻¹ = v at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact sourceQuietFixedSpan_ne_bot D
      ((sourceQuietFixedSpan_commutator D hmany hJ).symm.trans
        (commutator_eq_bot_iff_le_centralizer.mpr hc))
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (localOrbit T L) := isPerfect_iSup_conjugates L T
  let e : X ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨I,hIJ,hI⟩ := exists_isIrrPlus_le_of_not_fixed
    (ReducedNormal.representation H) X J hJX hn
  have hIW : ReducedNormal.subspaceImage H I ≤ sourceQuietFixedSpan D := by
    rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
    exact hIJ hv
  obtain ⟨E,hEI,_⟩ := lemma_3_2_3_constituent D.simpleQTKE T L D.maximal
    D.faithful D.quasisimple I hI
  have hTW : (T : Subgroup G) ≤ normalizer (sourceQuietFixedSpan D : Set G) :=
    (show (T : Subgroup G) ≤ H from le_sup_right).trans (sourceQuietFixedSpan_normalized D)
  have hseed : E.seed ≤ sourceQuietFixedSpan D := by
    apply (ReducedNormal.subspaceImage_mono H hEI).trans
    rw [ReducedNormal.subspaceImage_orbitSpan H T le_sup_right]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hIW hTW
  have hlocal : E.moduleSubgroup ≤ sourceQuietFixedSpan D :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hseed hTW
  exact ⟨E,hlocal,iSup_conjugates_le_of_le_normalizer _ _ _
    (hlocal.trans (sourceQuietFixedSpan_le D)) D.maximalLocal_normalizes_fullModule⟩

/-- Minimality retains the original full module and all module-independent data. -/
theorem sourceQuietFixedSpan_minimal_reselection
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.IsMinimalFullModule ∧ E.fullModule = D.fullModule ∧
      E.moduleSubgroup ≤ sourceQuietFixedSpan D := by
  obtain ⟨E,hl,hf⟩ := sourceQuietFixedSpan_reselection D hmany hJ
  have he := hmin.eq_of_le E hf
  refine ⟨E,?_,he,hl⟩
  intro F
  rw [he]
  exact hmin F

end CFSG.Quasithin.Chapter10
