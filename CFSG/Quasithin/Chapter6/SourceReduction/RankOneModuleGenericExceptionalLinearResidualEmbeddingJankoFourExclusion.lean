module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFourCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFourSmallAction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.SeedFusion

/-!
# Excluding the native J₄ graph section

The exceptional local component has nontrivial two-core. Its join with the
full Sylow therefore has a nontrivial minimal normal elementary subgroup.
Align the Sylow with the certified matrix Sylow. Minimality gives full
normalizer irreducibility, so the exhaustive outside-kernel calculation
places that elementary subgroup in the literal Mathieu kernel.

If it contains a 2B involution, its full normalizer lies in max1, already
excluded by the actual M₂₄ quotient. Otherwise the pure-kernel catalogue
bounds its order by sixteen. The small-action theorem makes the component
centralize it. A Sylow-fixed involution then puts both the component and
its full Sylow actor in the same involution centralizer. The second
centralizer has insufficient two-part; the first is excluded through the
surjective derived map to M₂₂ with its proved solvable kernel.

No maximal-subgroup coverage or nontrivial-core assertion for arbitrary
maximal subgroups is required. Source: Aschbacher–Smith A.3.12 and5.1.12,
printed pp.47–48 and635; the concrete Sylow catalogue follows
Kleidman–Wilson (1988), pp.484–510, with attribution in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open SylowCover SylowCover.KernelOrders SylowCover.OutsideKernelOrders
open Janko4 Janko4.LocalStructure.SylowNormalEights
open Janko4.OuterReduction.OddIndex
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup

private theorem not_exceptional_centralizer
    (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B))
    (z : Model) (hz : orderOf z = 2)
    (hBC : B ≤ centralizer ({z} : Set Model))
    (hSC : (S : Subgroup Model) ≤ centralizer ({z} : Set Model)) : False := by
  let C := centralizer ({z} : Set Model)
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with hf | hs
  · obtain ⟨e⟩ := hf
    open Janko4.OuterReduction.FixedGenerator.NormalizerSquares in
    let j := InvolutionCentralizers.First.centralizerEquiv.trans
      (((MulEquiv.subgroupCongr TwoCoreCentralizerData.localSubgroup_eq_top).trans
        Subgroup.topEquiv).symm.trans TwoCoreCentralizerData.sourceSubgroupEquivLocal.symm)
    let f := (e.trans j).toMonoidHom
    have hf : Function.Surjective f := (e.trans j).surjective
    let : Group.IsSolvable f.ker := by
      rw [(MonoidHom.ker_eq_bot_iff f).mpr (e.trans j).injective]
      infer_instance
    have hlC := local_restrict hl hBC
    have hnC : (S : Subgroup Model).subgroupOf C ≤ normalizer (B.subgroupOf C : Set C) := by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro b
      exact mem_normalizer_iff.mp (hn hs) (b : Model)
    have hmC := hm.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBC)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBC)))
    obtain ⟨hl',hn',hm'⟩ := Exceptional.local_section_map hlC hnC hmC f
    exact Max2Exclusion.not_exceptional_section_max2 ((S.subtype hSC).mapSurjective hf)
      ((B.subgroupOf C).map f) hl' hn' hm'
  · obtain ⟨e⟩ := hs
    have hd := card_dvd_of_le hSC
    rw [ambient_sylow_card, Nat.card_congr e.toEquiv,
      InvolutionCentralizers.Second.ambient_card] at hd
    norm_num at hd

private theorem small_elementary_gives_centralizer
    (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B))
    (hES : E ≤ S) (hEn : (S : Subgroup Model) ≤ normalizer (E : Set Model))
    (hEB : B ≤ normalizer (E : Set Model))
    [IsElementaryAbelian 2 E] (hne : E ≠ ⊥) (hc : Nat.card E ≤ 16) : False := by
  have hcent := exceptional_centralizes_small_elementary hl hm hc hEB
  let A := E.subgroupOf (S : Subgroup Model)
  have hAn : A.Normal := (normal_subgroupOf_iff_le_normalizer hES).mpr hEn
  let := hAn
  have hAne : A ≠ ⊥ := by
    intro h
    apply hne
    rw [← map_subgroupOf_eq_of_le hES]
    change A.map (S : Subgroup Model).subtype = ⊥
    rw [h,Subgroup.map_bot]
  have hI := center_inf_ne_bot_of_normal S.isPGroup' A hAne
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hI
  have hxS : (x : S) ≠ 1 := fun he => hx (Subtype.ext he)
  have hxG : ((x : S) : Model) ≠ 1 := fun he => hxS (Subtype.ext he)
  have hxe : ((x : S) : Model) ∈ E := x.property.2
  have hxo : orderOf ((x : S) : Model) = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨elemPow_eq_one_of_isElementaryAbelian _ hxe,hxG⟩
  apply not_exceptional_centralizer S B hl hn hm x hxo
  · intro b hb
    exact mem_centralizer_singleton_iff.mpr ((hcent hb) _ hxe).symm
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun y : S => (y : Model)) (mem_center_iff.mp x.property.1 ⟨s,hs⟩))

private theorem minimal_normal_image_irreducible
    (J : Subgroup Model) (E : Subgroup J) [E.Normal]
    (hmin : ∀ W : Subgroup J, W.Normal → W ≤ E → W = ⊥ ∨ W = E) :
    ClosureNormalizerIrreducible (E.map J.subtype) := by
  intro W hWE hNW
  have hWJ : W ≤ J := hWE.trans (map_subtype_le _)
  have hJN : J ≤ normalizer (E.map J.subtype : Set Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map J.subtype
  have hWn := (normal_subgroupOf_iff_le_normalizer hWJ).mpr (hJN.trans hNW)
  have hle : W.subgroupOf J ≤ E := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWJ]
    exact hWE
  rcases hmin (W.subgroupOf J) hWn hle with h | h
  · left
    rw [← map_subgroupOf_eq_of_le hWJ,h,Subgroup.map_bot]
  · right
    rw [← map_subgroupOf_eq_of_le hWJ,h]

private theorem reference_no_graph_section
    (S : Sylow 2 Model) (hS : (S : Subgroup Model) = twoSubgroup)
    (B : Subgroup Model) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hg : HasLinearFourGraphAction (S : Subgroup Model) B)
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B)) : False := by
  let J := B ⊔ (S : Subgroup Model)
  let U := (pCore 2 B).map B.subtype
  have hUn : J ≤ normalizer (U : Set Model) := sup_le
    (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
    (hn.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hU : U ≠ ⊥ := fun he => Exceptional.jankoFour_core_ne_bot S B hl hn hm
    (MulEquiv.refl _) ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hcore : pCore 2 J ≠ ⊥ := pCore_ne_bot_of_normalized_nontrivial J U
    ((map_subtype_le _).trans le_sup_left) (pCore_isPGroup.map B.subtype) hU hUn
  obtain ⟨E,hEn,hEne,hEc,hEe,hmin⟩ := exists_minimal_normal_le_pCore hcore
  let := hEn
  let := hEe
  let A := E.map J.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map J.subtype
  have hAN : J ≤ normalizer (A : Set Model) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map J.subtype
  have hAS : A ≤ (S : Subgroup Model) := by
    have he := (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal (S.subtype le_sup_right)
    rintro a ⟨e,heE,rfl⟩
    exact he heE
  have hAi := minimal_normal_image_irreducible J E hmin
  have hAK : A ≤ orderSpectrumKernel :=
    elementary_sylow_le_kernel_of_outside_certificates
      MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
      (outsideCatalogue_of_card presentation_card) matrixKernel_eq_orderSpectrumKernel
      rankCertificates A (hAS.trans hS.le) (hS ▸ (le_sup_right.trans hAN)) inferInstance hAi
  by_cases hseed : ∃ u ∈ A, IsConj u classSeed
  · obtain ⟨u,hu,huc⟩ := hseed
    have hJM := hAN.trans (normalizer_le_max1_of_seed_conjugate A hAK u hu huc)
    have he : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
      ext x
      simp
    apply jankoFour_graph_section_not_le_conjugate_max1 S B hl hn hg 1
    · rw [he,Subgroup.map_id]
      exact le_sup_right.trans hJM
    · rw [he,Subgroup.map_id]
      exact le_sup_left.trans hJM
  · have hpure : ∀ u ∈ A, ¬ IsConj u classSeed := by
      intro u hu hc
      exact hseed ⟨u,hu,hc⟩
    obtain ⟨i,hi⟩ := pureKernelCatalogue.1 A hAK (hS ▸ (le_sup_right.trans hAN)) hpure
    have hc : Nat.card A ≤ 16 := by
      rw [hi,pureKernelCatalogue.2 i]
      fin_cases i <;> decide
    have hAne : A ≠ ⊥ := fun he => hEne
      ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
    exact small_elementary_gives_centralizer S B A hl hn hm hAS
      (le_sup_right.trans hAN) (le_sup_left.trans hAN) hAne hc
/-- There is no full-Sylow-normalized exceptional graph section in the actual J₄.
The elementary subgroup and every native local exclusion are constructed. -/
theorem jankoFour_no_graph_section
    (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B)) :
    ¬ HasLinearFourGraphAction (S : Subgroup Model) B := by
  intro hgraph
  let P : Sylow 2 Model := Sylow.ofCard twoSubgroup
    (twoSubgroup_card.trans ((ambient_sylow_card S).symm.trans S.card_eq_multiplicity))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S P
  let e := MulAut.conj g
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup Model) = twoSubgroup := congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  obtain ⟨hl',hn',hm'⟩ := Exceptional.local_section_map hl hn hm e.toMonoidHom
  have hk : IsPGroup 2 (e.toMonoidHom.subgroupMap B).ker :=
    IsPGroup.ker_isPGroup_of_injective (e.subgroupMap B).injective
  exact reference_no_graph_section Q hQ (B.map e.toMonoidHom) hl' hn'
    (hgraph.map_of_two_kernel hn e.toMonoidHom hk) hm'

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
