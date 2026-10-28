module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveWreathExclusion.ComponentActions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefDisplacement
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefG2Exclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefShortExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveComparison
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveQuotient
public import Theory.Quasithin.TwoKernelImage

/-!
# Retained source data for the marked-five wreath exclusion

The same component K of the original H is used in both core cases. The
nontrivial-core case uses exactly W → W/O₂(W), with both local factors and
the common Sylow subgroup mapped by this quotient. The source comparison
supplies characteristic two for both quotient parabolics.

The original H-span is retained, with its order bound and the two actual
paired chief actions supplied by `marked_five_wreath_chief_actions`.
Both moved chief factors also force |[O₂(K),K]| ≥ 256 on this same K,
excluding the natural L₂(4) and A₅ block types before the quotient passage.
The same original elementary span excludes the first G₂ local and its central
two-covers at K in both generated-core cases. Both chief intervals remain
moved on K, excluding every short structure on that same component,
including the orthogonal block alternatives with central fixed layers.
In particular no arbitrary existential ambient pair replaces this data.

This is a reduction of original 15.2.4, not its completion. The remaining
mixed-pair recognition/exclusion must use the actual source hypotheses.
Source: Aschbacher--Smith, original 15.2.4, printed pp.1105--1107, with
F.1.12 on pp.262--264 and the C.2.7/A.3.15 comparison on p.1107.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The marked-five wreath hypothesis gives both literal source branches, keeping
its original H-span and the same component K throughout the quotient passage. -/
theorem ChosenSmallSource.marked_five_wreath_source_reduction
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    65536 ≤ Nat.card (conjugateSpan H V) ∧
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (M ⊓ Mc).pCoreIn 2 ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧ IsQuasithin (W ⧸ pCore 2 W) ∧
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
        (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
          Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
        Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
        Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  let := h.prepared.elementary
  intro l hd
  refine ⟨h.marked_five_wreath_span_card hH he l hd,?_⟩
  dsimp only
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨source_dihedral_five_join_quotient h.ambient T h.empty h.maximal h.centralizing
    h.partner h.many h.prepared l hp hd,?_⟩
  obtain ⟨K,hK,heK,hout,hi,hJS,hpar⟩ := source_HStar_wreath_five_quotient_parabolics
    h.ambient T h.empty h.maximal h.centralizing h.partner h.many h.prepared h.small hH he
  have hlocal := source_dihedral_five_mixed_local_data h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared l hd hH he hK heK hi
  have hRS := source_HStar_wreath_intersection_core_le_component_normalizer
    h.ambient T h.maximal h.centralizing h.partner h.prepared hH he hK
  refine ⟨K,hK,heK,hout,hi,hJS,hRS,hlocal.1,hlocal.2.2,?_⟩
  intro hcore
  have hSyl := source_dihedral_five_nontrivial_core_sylow h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared l hd hout hi hJS hcore
  have hquot := source_dihedral_five_core_quotient_configuration h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared l hd hH he hK heK hi hout hJS hcore (hpar hcore)
  exact ⟨hSyl,(h.ambient.quasithin.subgroup _).quotient_twoSubgroup _ pCore_isPGroup,hquot⟩

/-- The same component used in both original core cases contains the
contributions of both noncentral chief factors. The bounds are established
before passage to W/O₂(W); the source recognition still has to exclude
these configurations, and remains with qt-e-152-small-parabolic. -/
theorem ChosenSmallSource.marked_five_wreath_source_reduction_with_component_bounds
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    65536 ≤ Nat.card (conjugateSpan H V) ∧
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      256 ≤ Nat.card (conjugateSpan H V ⊓ K : Subgroup G) ∧
      256 ≤ Nat.card (pCore 2 K) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (M ⊓ Mc).pCoreIn 2 ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧ IsQuasithin (W ⧸ pCore 2 W) ∧
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
        (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
          Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
        Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
        Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  let := h.prepared.elementary
  intro l hd
  obtain ⟨hU,hL,K,hK,hrest⟩ := h.marked_five_wreath_source_reduction hH he l hd
  obtain ⟨hc,hp⟩ := h.marked_five_wreath_component_bounds hH he hK l hd
  exact ⟨hU,hL,K,hK,hc,hp,hrest⟩

/-- Both source core cases keep the actual component's large commutator
layer and exclude its two natural block types. These statements concern K
before passage to W/O₂(W); no survival through that quotient is assumed. -/
theorem ChosenSmallSource.marked_five_wreath_source_reduction_with_displacement
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    65536 ≤ Nat.card (conjugateSpan H V) ∧
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) ∧
      256 ≤ Nat.card (ChapterC.blockU K) ∧
      ¬ ChapterC.IsL2EvenBlock K 2 ∧ ¬ ChapterC.IsAlternatingBlock K 5 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (M ⊓ Mc).pCoreIn 2 ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧ IsQuasithin (W ⧸ pCore 2 W) ∧
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
        (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
          Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
        Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
        Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  let := h.prepared.elementary
  intro l hd
  obtain ⟨hU,hL,K,hK,hrest⟩ := h.marked_five_wreath_source_reduction hH he l hd
  have hm := h.marked_five_wreath_component_displacement hH he hK l hd
  have hn := h.marked_five_wreath_component_not_blocks hH he hK l hd
  exact ⟨hU,hL,K,hK,hm.1,hm.2,hn.1,hn.2,hrest⟩

/-- Both original generated-core cases exclude the first G₂ local and its
central two-covers at the same embedded component K. The conclusion keeps
the literal quotient images; no chief-factor survival through O₂(W) is used. -/
theorem ChosenSmallSource.marked_five_wreath_source_reduction_no_g2_short_cover
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (F : Type*) [Field F] [CharP F 2] [Finite F] (hq : 2 < Nat.card F) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    65536 ≤ Nat.card (conjugateSpan H V) ∧
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) ∧
      256 ≤ Nat.card (ChapterC.blockU K) ∧
      ¬ ChapterC.IsL2EvenBlock K 2 ∧ ¬ ChapterC.IsAlternatingBlock K 5 ∧
      (¬ ∃ f : K →* Atlas.G2.LieParabolicSetup.local₁ (F := F),
        Function.Surjective f ∧ f.ker ≤ center K ∧ IsPGroup 2 f.ker) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (M ⊓ Mc).pCoreIn 2 ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧ IsQuasithin (W ⧸ pCore 2 W) ∧
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
        (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
          Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
        Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
        Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  let := h.prepared.elementary
  intro l hd
  obtain ⟨hU,hL,K,hK,hrest⟩ := h.marked_five_wreath_source_reduction hH he l hd
  have hm := h.marked_five_wreath_component_displacement hH he hK l hd
  have hn := h.marked_five_wreath_component_not_blocks hH he hK l hd
  have hg := h.marked_five_wreath_component_no_g2_short_cover hH he hK F hq l hd
  exact ⟨hU,hL,K,hK,hm.1,hm.2,hn.1,hn.2,hg,hrest⟩

/-- Both original core cases retain a non-short actual component. This
excludes every short-block row before quotienting, and keeps the original
quotient maps for the remaining mixed-pair recognition. -/
theorem ChosenSmallSource.marked_five_wreath_source_reduction_nonshort
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    65536 ≤ Nat.card (conjugateSpan H V) ∧
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧ ¬ ChapterC.IsShort K ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (M ⊓ Mc).pCoreIn 2 ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧ IsQuasithin (W ⧸ pCore 2 W) ∧
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
        (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
          Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
        Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
        Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) := by
  let := h.prepared.elementary
  intro l hd
  obtain ⟨hU,hL,K,hK,hrest⟩ := h.marked_five_wreath_source_reduction hH he l hd
  exact ⟨hU,hL,K,hK,h.marked_five_wreath_component_not_short hH he hK l hd,hrest⟩

end CFSG.Quasithin.Chapter15.Section02
