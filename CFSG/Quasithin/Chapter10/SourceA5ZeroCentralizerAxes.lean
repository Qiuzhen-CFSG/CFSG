module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroPairedModules
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveCrossCentralizers
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualCentralizers
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveActorCorrection

/-!
# Actual centralizers covering the opposite symmetric-five axes

The marked opposite factor fixes the original block layer. Every actor in
its preimage normalizes that block, so the genuine A₅ cocycle correction
adjusts it by a kernel element into the block centralizer. This proves
surjectivity onto the opposite full S₅ axis. The quotient centralizer
calculation gives the reverse containment, with the same marking retained.

This identifies actual groups for the extension-splitting step in the
zero-center branch of Aschbacher–Smith 10.2.1, pp.742–743; it does not yet
construct their S₅ sections or the four-dihedral-factor endgame.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
private theorem corrected_centralizer_image
    {X K : Type*} [Group X] [Group K] (q : X →* K)
    (A P F : Subgroup X) (hA : IsAlternatingBlock A 5)
    (hn : P ≤ normalizer (A : Set X))
    (hF : F ≤ P) (hc : F ≤ centralizer ((blockU A).map A.subtype : Set X))
    (hk : (blockU A).map A.subtype ≤ q.ker) (hkp : q.ker ≤ P) :
    F.map q ≤ (P ⊓ centralizer (A : Set X)).map q := by
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨u,hu⟩ := hA.exists_centralizing_correction g (hn (hF hg)) (hc hg)
  have hum : ((u:A):X) ∈ (blockU A).map A.subtype := mem_map_of_mem A.subtype u.property
  refine ⟨((u:A):X)*g,⟨P.mul_mem (hkp (hk hum)) (hF hg),hu⟩,?_⟩
  rw [map_mul,(MonoidHom.mem_ker.mp (hk hum)),one_mul]

/-- The actual block centralizer covers the opposite full S₅ factor of the same marking. -/
@[expose] def SourceZeroOriginalCentralizerAxes : Prop :=
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  letI := offenderSubgroup_normal α
  let A := L.subgroupOf H
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ _c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
      Y.comap q ≤ normalizer (A : Set H) ∧
      ((A.map q = (factorResidual q Y d.first).map q ∧
        (Y.comap q ⊓ centralizer (A : Set H)).map q = d.second.map Y.subtype) ∨
       (A.map q = (factorResidual q Y d.second).map q ∧
        (Y.comap q ⊓ centralizer (A : Set H)).map q = d.first.map Y.subtype))

set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_original_centralizer_axes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    SourceZeroOriginalCentralizerAxes D := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨d,c,hex,hN,haxes⟩ := source_a5_original_paired_axes D e hn hout
  have hcross := paired_cross_module_centralizers U q hq hk d c
  have hA := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.1
  have hU : (blockU A).map A.subtype ≤ U := by
    rw [←source_a5_zero_original_block_moved D e hn hout hz]
    exact commutator_le_left _ _
  have hUk : (blockU A).map A.subtype ≤ q.ker := by
    rw [hk]
    exact hU.trans U.le_centralizer
  have hkp : q.ker ≤ Y.comap q := ker_le_comap q Y
  have hm (F : Subgroup H) (he : A.map q = F.map q) :
      (blockU A).map A.subtype = ⁅U,F⁆ := by
    have he' : NormalElementaryQuotient.commutatorSpace U A =
        NormalElementaryQuotient.commutatorSpace U F := by
      rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
        NormalElementaryQuotient.commutatorSpace_eq U q hq hk,he]
    have hh : (⁅U,A⁆ : Subgroup H) = ⁅U,F⁆ := by
      apply le_antisymm
      · intro x hx
        have hv : Additive.ofMul (⟨x,(commutator_le_left U A) hx⟩ : U) ∈
            NormalElementaryQuotient.commutatorSpace U A := hx
        rw [he'] at hv
        exact hv
      · intro x hx
        have hv : Additive.ofMul (⟨x,(commutator_le_left U F) hx⟩ : U) ∈
            NormalElementaryQuotient.commutatorSpace U F := hx
        rw [←he'] at hv
        exact hv
    exact (source_a5_zero_original_block_moved D e hn hout hz).symm.trans hh
  have hmap : (Y.comap q ⊓ centralizer (A : Set H)).map q ≤
      Y ⊓ centralizer (A.map q : Set (H ⧸ C)) :=
    le_inf ((map_mono inf_le_left).trans (map_comap_le q Y))
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ q))
  refine ⟨d,c,hex,hN,?_⟩
  rcases haxes with ha | ha
  · refine Or.inl ⟨ha,le_antisymm ?_ ?_⟩
    · have hc := paired_symmetric_first_residual_centralizer α q hq d c
      rw [←ha] at hc
      exact hmap.trans_eq hc
    · have hc := corrected_centralizer_image q A (Y.comap q)
        (factorPreimage q Y d.second) hA hN
        (comap_mono (map_subtype_le _)) (by rw [hm _ ha]; exact hcross.1) hUk hkp
      rw [factorPreimage,map_comap_eq_self_of_surjective hq] at hc
      exact hc
  · refine Or.inr ⟨ha,le_antisymm ?_ ?_⟩
    · have hc := paired_symmetric_second_residual_centralizer α q hq d c
      rw [←ha] at hc
      exact hmap.trans_eq hc
    · have hc := corrected_centralizer_image q A (Y.comap q)
        (factorPreimage q Y d.first) hA hN
        (comap_mono (map_subtype_le _)) (by rw [hm _ ha]; exact hcross.2) hUk hkp
      rw [factorPreimage,map_comap_eq_self_of_surjective hq] at hc
      exact hc
end CFSG.Quasithin.Chapter10
