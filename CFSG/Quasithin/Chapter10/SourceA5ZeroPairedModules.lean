module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerBaumann
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveModules

/-!
# Natural coordinates on the original zero-center block layer

In the zero-centralizer branch the reduced local module is the full two-core.
Its commutator with the original block is therefore the block's intrinsic
U-layer. Locating that block on a marked quotient axis identifies this literal
layer with one of the two natural-module sections, including the full product
action and the original subgroup inclusion.
Source: Aschbacher–Smith, 10.2.1, pp.742–743, using E.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_original_block_moved
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let A := L.subgroupOf H
    ⁅D.moduleSubgroup.subgroupOf H,A⁆ = (blockU A).map A.subtype := by
  let H := localJoin T L
  have hu : D.moduleSubgroup.subgroupOf H = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  change ⁅D.moduleSubgroup.subgroupOf H,L.subgroupOf H⁆ = _
  rw [hu]
  exact (source_a5_original_block_of_baumann_not_controlled D e hn hout).1.ambient_core_commutator

/-- The same marked product carries actual natural coordinates on the original block layer. -/
@[expose] def SourceZeroOriginalLayerCoordinates : Prop :=
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let V := AddSubgroup.toZModSubmodule 2
    (((blockU A).map A.subtype).subgroupOf U).toAddSubgroup
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
    ∃ s₁ s₂ : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] Additive U,
      (∀ v, c.symmetricCoreMap (s₁ v) = (v,0)) ∧
      (∀ v, c.symmetricCoreMap (s₂ v) = (0,v)) ∧
      (∀ g : Y, ∀ v,
        s₁ (BinaryPermutation.coreRepresentation (Fin 5) (c.action.groupEquiv g).1 v) =
          α (g : H ⧸ C) (s₁ v)) ∧
      (∀ g : Y, ∀ v,
        s₂ (BinaryPermutation.coreRepresentation (Fin 5) (c.action.groupEquiv g).2 v) =
          α (g : H ⧸ C) (s₂ v)) ∧
      s₁.range = NormalElementaryQuotient.commutatorSpace U (factorResidual q Y d.first) ∧
      s₂.range = NormalElementaryQuotient.commutatorSpace U (factorResidual q Y d.second) ∧
      Y.comap q ≤ normalizer (A : Set H) ∧
      ((A.map q = (factorResidual q Y d.first).map q ∧ s₁.range = V) ∨
        (A.map q = (factorResidual q Y d.second).map q ∧ s₂.range = V))

set_option backward.isDefEq.respectTransparency false in
theorem source_a5_zero_original_layer_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    SourceZeroOriginalLayerCoordinates D := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨d,c,_,hN,hA⟩ := source_a5_original_paired_axes D e hn hout
  obtain ⟨s₁,s₂,h₁,h₂,he₁,he₂,hr₁,hr₂⟩ :=
    paired_symmetric_residual_module_sections U q hq hk d c
  have hm : NormalElementaryQuotient.commutatorSpace U A =
      AddSubgroup.toZModSubmodule 2
        (((blockU A).map A.subtype).subgroupOf U).toAddSubgroup := by
    unfold NormalElementaryQuotient.commutatorSpace
    rw [source_a5_zero_original_block_moved D e hn hout hz]
  refine ⟨d,c,s₁,s₂,h₁,h₂,he₁,he₂,hr₁,hr₂,hN,?_⟩
  rcases hA with hA | hA
  · refine Or.inl ⟨hA,?_⟩
    rw [hr₁,←hm,NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
      NormalElementaryQuotient.commutatorSpace_eq U q hq hk,hA]
  · refine Or.inr ⟨hA,?_⟩
    rw [hr₂,←hm,NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
      NormalElementaryQuotient.commutatorSpace_eq U q hq hk,hA]

end CFSG.Quasithin.Chapter10
