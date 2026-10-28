module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Product
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Placement
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryKnownSimple

/-!
# Nonenlargement of the original two relative components

The actual core P is normal in G_P, so both intrinsic two-cores lie in
O₂(G_P). Thus the literal images of K and L₂ in G_P/O₂(G_P) are their
intrinsic binary PSL₂ quotients. The original Sylow normalizes each image,
and genuine local-family membership survives this quotient.

The proved known-simple binary component selection theorem says that a
proper enlargement of either image forces field degree two. The source's
odd degree excludes this. Lifting equality puts the containing component
inside the original component-Sylow join, where C-component minimality
proves equality. Every normality assertion is relative to G_P.

This is a specialized A.3.12 route using the actual source normalization;
no universal embedding classifier or component-recognition premise is
assumed. Orthogonal.Complete consumes both conclusions and discharges all
remaining local callbacks. Source: Aschbacher--Smith, printed p.774.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem odd_binary_nonenlargement
    {J : Type*} [Group J] [Finite J]
    (hJ : IsSQTK KnownSimple.IsKnownSimple J) (S : Sylow 2 J)
    {B C : Subgroup J} (hB : B ∈ Chapter1.L J S)
    (hC : C.IsCComponent) (hBC : B ≤ C)
    (hSB : (S : Subgroup J) ≤ normalizer (B : Set J))
    (hcore : B.pCoreIn 2 ≤ pCore 2 J)
    {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : B = C := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let U := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let B' := B.map q
  let C' := C.map q
  let a := q.subgroupMap B
  have hk : a.ker = pCore 2 B := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact le_antisymm (le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩)
      (map_le_iff_le_comap.mp hcore)
  let e : (B ⧸ pCore 2 B) ≃* B' :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective a (q.subgroupMap_surjective B))
  have hm' : ClassicalGroup.IsPSL B' 2 (2^n) := hm.of_mulEquiv e.symm
  let : Group.IsPerfect B := Chapter1.mem_L_isPerfect hB
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := a) (q.subgroupMap_surjective B)
  let : IsSimpleGroup B' :=
    ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_simple hn hm'
  have hz : center B' = ⊥ :=
    ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_center_eq_bot hm'
  let : IsQuasisimple B' := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let := pCore_isNilpotent (p := 2) (G := J)
  have hl : B' ∈ ChapterA.Section03.localCComponents U := by
    simpa only [U,B',q,Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
  have he : B' = C' := by
    rcases ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_larger_selection_knownSimple
      (ChapterE.Structure.sqtk_two_quotient hJ (pCore 2 J) pCore_isPGroup)
      (pCore_quotient_pCore_eq_bot 2) U hl (hC.map_quotient _) (map_mono hBC)
      ((map_mono hSB).trans (le_normalizer_map q)) hn hm' with he | ⟨hn2,_⟩
    · exact he
    · have hh : Odd (2 : ℕ) := hn2 ▸ ho
      norm_num at hh
  have hCQ : C ≤ B ⊔ pCore 2 J := by
    have hh : C ≤ (B.map q).comap q := map_le_iff_le_comap.mp he.symm.le
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hCS : C ≤ B ⊔ (S : Subgroup J) := hCQ.trans
    (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) B)
  have hh := hB.1.eq_of_le (hC.subgroupOf hCS) (comap_mono hBC)
  simpa only [map_subgroupOf_eq_of_le (show B ≤ B ⊔ (S : Subgroup J) from le_sup_left),
    map_subgroupOf_eq_of_le hCS] using congrArg (map (B ⊔ (S : Subgroup J)).subtype) hh

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- P lies in O₂(G_P) because it is an actual normal two-subgroup. -/
theorem source_pairCore_le_normalizer_core :
    (pairCore V H h).subgroupOf (coreNormalizer V H h) ≤
      pCore 2 (coreNormalizer V H h) := by
  let : ((pairCore V H h).subgroupOf (coreNormalizer V H h)).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have hp : IsPGroup 2 (pairCore V H h) := by
    rw [← d.residual_core]
    exact isPGroup_pCoreIn 2 _
  exact le_sSup ⟨inferInstance,hp.comap_subtype⟩

/-- The original K is its normal containing C-component in G_P. -/
theorem source_residual_normal_component :
    Source.NormalComponentIn (coreNormalizer V H h) (outsideResidual H) := by
  obtain ⟨C,hC,hKC,_⟩ := source_residual_containing_component d
  let N := coreNormalizer V H h
  have hKN := source_residual_le_coreNormalizer d
  let B := (outsideResidual H).subgroupOf N
  let E := C.subgroupOf N
  let U := T.subtype (sylow_le_coreNormalizer f d.local_core)
  have he : B = E := by
    apply odd_binary_nonenlargement
      (S.source.simpleQTKE.twoLocal_sqtk
        (coreNormalizer_twoLocal f d.conjugator_mem d.axis_eq_plane)) U
      (source_residual_mem_normalizer_local d) hC.1.2 (comap_mono hKC)
    · rw [← subgroupOf_normalizer_eq hKN]
      exact comap_mono (d.source.outside.1.1.2.trans (outsideResidual_normalized H))
    · rw [pCoreIn_subgroupOf _ _ _ hKN,d.residual_core]
      exact source_pairCore_le_normalizer_core d
    · exact S.nonbinary
    · exact source_degree_odd d
    · let b := subgroupOfEquivOfLe hKN
      let e := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
        (d.pair_natural.quotientEquiv.trans
          (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := d.pair_field.Carrier)))
      exact ⟨d.pair_field.Carrier,inferInstance,inferInstance,
        by rw [d.pair_field.card_eq,d.pair_degree],⟨e⟩⟩
  have heG : outsideResidual H = C := by
    have hh := congrArg (map N.subtype) he
    change ((outsideResidual H).subgroupOf N).map N.subtype =
      (C.subgroupOf N).map N.subtype at hh
    rw [map_subgroupOf_eq_of_le (show outsideResidual H ≤ N from hKN),
      map_subgroupOf_eq_of_le (show C ≤ N from hC.1.1)] at hh
    exact hh
  exact heG.symm ▸ hC

/-- The original L₂ is its normal containing C-component in G_P. -/
theorem source_local_normal_component :
    Source.NormalComponentIn (coreNormalizer V H h) (f.Li 1) := by
  obtain ⟨C,hC,hLC,_⟩ := source_local_containing_component d
  let N := coreNormalizer V H h
  have hLN : f.Li 1 ≤ N := le_sup_left.trans
    (orthogonalJoin_le_coreNormalizer d.source d.conjugator_mem (f.Li 1) d.local_core)
  let B := (f.Li 1).subgroupOf N
  let E := C.subgroupOf N
  let U := T.subtype (sylow_le_coreNormalizer f d.local_core)
  have he : B = E := by
    apply odd_binary_nonenlargement
      (S.source.simpleQTKE.twoLocal_sqtk
        (coreNormalizer_twoLocal f d.conjugator_mem d.axis_eq_plane)) U
      (source_local_mem_normalizer_local d) hC.1.2 (comap_mono hLC)
    · rw [← subgroupOf_normalizer_eq hLN]
      exact comap_mono (f.sylow_normalizes_Li 1)
    · rw [pCoreIn_subgroupOf _ _ _ hLN,d.local_core]
      exact source_pairCore_le_normalizer_core d
    · exact S.nonbinary
    · exact source_degree_odd d
    · let b := subgroupOfEquivOfLe hLN
      let e := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
        (SL3.flagLocalCoreEquiv S m f 1)
      exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have heG : f.Li 1 = C := by
    have hh := congrArg (map N.subtype) he
    change ((f.Li 1).subgroupOf N).map N.subtype =
      (C.subgroupOf N).map N.subtype at hh
    rw [map_subgroupOf_eq_of_le hLN,
      map_subgroupOf_eq_of_le (show C ≤ N from hC.1.1)] at hh
    exact hh
  exact heG.symm ▸ hC

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
