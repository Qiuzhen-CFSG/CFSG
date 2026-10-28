module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.IntrinsicTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Reduction
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.GroupTheory.PCoreImage

/-!
# The literal local section as an octad preimage residual

The certified quotient map from max1 to native M₂₄ preserves both the
L₄(2) section and Sylow-local C-component membership. Common-octad
placement therefore identifies the image with the octad stabilizer.
The Sylow subgroup contains the quotient kernel, so the generated
local overgroup is the full octad preimage. Subnormality and perfectness
then identify the original section with that preimage's solvable residual.
No splitting or equality of the section with the full preimage is used.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48; the local
configuration used in 1.3.9, printed p.514; GLS3 Table 5.3i.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

@[expose] noncomputable def literalMathieuMap : certifiedMathieuSubgroup →* M24 :=
  certifiedMathieuQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 certifiedMathieuSubgroup))

theorem literalMathieuMap_surjective : Function.Surjective literalMathieuMap :=
  certifiedMathieuQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem literalMathieuMap_ker : literalMathieuMap.ker = pCore 2 certifiedMathieuSubgroup := by
  ext x
  change certifiedMathieuQuotientEquiv (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff _ certifiedMathieuQuotientEquiv.injective]
  exact QuotientGroup.eq_one_iff x


@[expose] noncomputable def literalOctadPreimage (O : Octad) : Subgroup certifiedMathieuSubgroup :=
  (octadStabilizer O).comap literalMathieuMap

@[expose] noncomputable def literalOctadResidual (O : Octad) : Subgroup certifiedMathieuSubgroup :=
  (solvableResidual (literalOctadPreimage O)).map (literalOctadPreimage O).subtype

@[expose] noncomputable def literalOctadTwoPreimage (O : Octad) : Subgroup certifiedMathieuSubgroup :=
  ((octadStabilizer O).pCoreIn 2).comap literalMathieuMap

theorem literalCore_elementary : IsElementaryAbelian 2 (pCore 2 certifiedMathieuSubgroup) := by
  change IsElementaryAbelian 2
    (pCore 2 (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
  rw [← Janko4.LocalStructure.localKernel_eq_twoCore]
  exact Janko4.LocalStructure.localKernel_elementary _ _

theorem literalCore_card : Nat.card (pCore 2 certifiedMathieuSubgroup) = 2048 := by
  change Nat.card
    (pCore 2 (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) = _
  rw [← Janko4.LocalStructure.localKernel_eq_twoCore]
  exact Janko4.Cardinality.localKernel_card _ _

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

theorem literalOctadCore_card_le (O : Octad) : Nat.card ((octadStabilizer O).pCoreIn 2) ≤ 16 := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  have hs : octadStabilizer O =
      (octadStabilizer LinearFourCore.seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val =
      (MulAction.stabilizer M24 LinearFourCore.seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let e : octadStabilizer LinearFourCore.seedOctad ≃* octadStabilizer O :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  rw [pCoreIn, card_map_of_injective (octadStabilizer O).subtype_injective,
    ← pCore_map_iso 2 e, card_map_of_injective e.injective]
  exact (card_le_of_le LinearFourCore.core_le_kernel).trans_eq LinearFourCore.kernel_card

theorem literalOctadResidual_image (O : Octad) :
    (literalOctadResidual O).map literalMathieuMap = octadStabilizer O := by
  let := (LinearFourCore.octad_core_structure O).1
  change ((solvableResidual ((octadStabilizer O).comap literalMathieuMap)).map
    ((octadStabilizer O).comap literalMathieuMap).subtype).map literalMathieuMap = _
  rw [map_solvableResidual_comap literalMathieuMap literalMathieuMap_surjective,
    solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

theorem literalOctadResidual_coreImage (O : Octad) :
    ((literalOctadResidual O).pCoreIn 2).map literalMathieuMap =
      (octadStabilizer O).pCoreIn 2 := by
  have hk : IsPGroup 2 literalMathieuMap.ker := by
    rw [literalMathieuMap_ker]
    exact pCore_isPGroup
  rw [map_pCoreIn_of_ker_isPGroup literalMathieuMap hk, literalOctadResidual_image]

private noncomputable def quotientCoreEquiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : G ⧸ pCore 2 G ≃* H ⧸ pCore 2 H := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : pCore 2 G = q.ker := by
    change pCore 2 G = ((QuotientGroup.mk' (pCore 2 H)).ker).comap f
    rw [QuotientGroup.ker_mk']
    exact (f.comap_pCore_of_ker_isPGroup hf hk).symm
  exact QuotientGroup.liftEquiv _ hq he

noncomputable def literalImageSectionEquiv (B : Subgroup certifiedMathieuSubgroup) :
    XiQuotient B ≃* XiQuotient (B.map literalMathieuMap) := by
  apply quotientCoreEquiv (literalMathieuMap.subgroupMap B)
    (literalMathieuMap.subgroupMap_surjective B)
  rw [Subgroup.ker_subgroupMap, literalMathieuMap_ker]
  exact pCore_isPGroup.comap_subtype

theorem literalImage_isPSL (B : Subgroup certifiedMathieuSubgroup)
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2) :
    ClassicalGroup.IsPSL (XiQuotient (B.map literalMathieuMap)) 4 2 :=
  hB.of_mulEquiv (literalImageSectionEquiv B).symm

theorem literalImage_local (B : Subgroup certifiedMathieuSubgroup)
    (T : Sylow 2 certifiedMathieuSubgroup)
    (hlocal : B ∈ ChapterA.Section03.localCComponents T) :
    B.map literalMathieuMap ∈ ChapterA.Section03.localCComponents
      (T.mapSurjective literalMathieuMap_surjective : Sylow 2 M24) := by
  let : Group.IsSolvable literalMathieuMap.ker := by
    rw [literalMathieuMap_ker]
    let := pCore_isNilpotent (p := 2) (G := certifiedMathieuSubgroup)
    infer_instance
  exact Section02.localCComponents_map_of_solvable_ker hlocal literalMathieuMap

theorem literalImage_eq_octad (hOctad : MathieuLocalSections.OctadPlacement)
    (B : Subgroup certifiedMathieuSubgroup) (T : Sylow 2 certifiedMathieuSubgroup)
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2)
    (hlocal : B ∈ ChapterA.Section03.localCComponents T) :
    ∃ O : Octad, B.map literalMathieuMap = octadStabilizer O ∧
      B ⊔ T.toSubgroup ≤ literalOctadPreimage O := by
  let S := T.mapSurjective literalMathieuMap_surjective
  have hB' := literalImage_isPSL B hB
  have hlocal' := literalImage_local B T hlocal
  obtain ⟨O, hO⟩ := hOctad _ S hB' hlocal'
  refine ⟨O, MathieuLocalSections.eq_of_local_of_join_le _ _ S hB' hlocal' hO
    (octadStabilizer_card O) (LinearFourCore.octad_core_structure O).1, ?_⟩
  apply map_le_iff_le_comap.mp
  rw [Subgroup.map_sup]
  exact hO

theorem literalJoin_eq_preimage (B : Subgroup certifiedMathieuSubgroup)
    (T : Sylow 2 certifiedMathieuSubgroup) (O : Octad)
    (him : B.map literalMathieuMap = octadStabilizer O)
    (hle : B ⊔ T.toSubgroup ≤ literalOctadPreimage O) :
    B ⊔ T.toSubgroup = literalOctadPreimage O := by
  apply le_antisymm hle
  change (octadStabilizer O).comap literalMathieuMap ≤ _
  rw [← him, comap_map_eq, literalMathieuMap_ker]
  exact sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal T) B

theorem literalLocal_eq_residual (B : Subgroup certifiedMathieuSubgroup)
    (T : Sylow 2 certifiedMathieuSubgroup) (O : Octad)
    (hlocal : B ∈ ChapterA.Section03.localCComponents T)
    (him : B.map literalMathieuMap = octadStabilizer O)
    (hle : B ⊔ T.toSubgroup ≤ literalOctadPreimage O) :
    B = literalOctadResidual O := by
  have hj := literalJoin_eq_preimage B T O him hle
  have hBH : B ≤ literalOctadPreimage O := le_sup_left.trans hle
  have hc : (B.subgroupOf (literalOctadPreimage O)).IsCComponent := by
    rw [← hj]
    exact hlocal
  have hsup : B ⊔ pCore 2 certifiedMathieuSubgroup = literalOctadPreimage O := by
    rw [← literalMathieuMap_ker, ← comap_map_eq, him]
    rfl
  let N := (pCore 2 certifiedMathieuSubgroup).subgroupOf (literalOctadPreimage O)
  let : N.Normal := inferInstance
  let : Group.IsSolvable N := by
    have hp : IsPGroup 2 N := pCore_isPGroup.comap_subtype
    let := hp.isNilpotent
    infer_instance
  let := hc.perfect
  have htop : B.subgroupOf (literalOctadPreimage O) ⊔ N = ⊤ := by
    rw [← subgroupOf_sup hBH (show pCore 2 certifiedMathieuSubgroup ≤ literalOctadPreimage O
      from hsup ▸ le_sup_right), hsup, subgroupOf_self]
  have he := hc.subnormal.eq_solvableResidual_of_sup_eq_top N htop
  have hm := congrArg (Subgroup.map (literalOctadPreimage O).subtype) he
  simpa only [map_subgroupOf_eq_of_le hBH, literalOctadResidual] using hm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
