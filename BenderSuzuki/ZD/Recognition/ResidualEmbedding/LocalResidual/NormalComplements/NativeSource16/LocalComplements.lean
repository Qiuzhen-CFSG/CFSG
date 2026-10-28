module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.CentralizerOrder
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OuterSylow
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Normalizer

/-!
# Corollary 16.6 and Lemma 16.7 from the preceding rank-one proposition

The original source selection provides the marked involution, its maximal
trace, and the centralizer Sylow with a distinguished central involution.
Involution placement supplies the Sylow census and global fusion. The fused
centralizer has Sylow order two, and the recognized perfect circle has cyclic
outer Sylow subgroups. The actual outer-action argument then proves normal
two-complements and cyclic Sylow subgroups for every trivial-circle subgroup.
The normalizer theorem and the original internal two-point complement follow.

Only the genuine preceding Proposition 16.5 remains explicit. No local model,
Omega identity, involution fusion, centralizer size or outer-action conclusion
is assumed at this source interface.

Source: GLS IV, Chapter 2, Corollary 16.6 and Lemma 16.7.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Full Corollary 16.6(e) from the original residual setup and the genuine
preceding rank-one Proposition 16.5. All marked source data is constructed. -/
public theorem source16_local_complements_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hrank : ∀ t ∈ Z, t ∉ M → ¬ TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    ∀ Y : Subgroup G, localCircle Z Y = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S := by
  obtain ⟨t₀,ht₀,ht₀M⟩ := exists_not_mem h.disconnected
  obtain ⟨u,t,huD,hu,_,ht,htM,htu,_,hmax,S,huT,z,hz,hzT,hTz,T,hT⟩ :=
    exists_source_centralizer_configuration h.disconnected r ha hn ht₀ ht₀M
  let B := centralizer ({u} : Set G)
  let H := B ⊓ M
  let T₁ := (S : Subgroup H).map H.subtype
  have hTM : T₁ ≤ M := (map_subtype_le _).trans inf_le_right
  have hzM : z ∈ M := hTM hzT
  have hzu : Commute z u := (mem_centralizer_singleton_iff.mp (hTz huT)).symm
  have hTM' : (T : Subgroup B).map B.subtype ≤ M := hT.symm ▸ hTM
  have huT' : u ∈ (T : Subgroup B).map B.subtype := hT.symm ▸ huT
  have hTz' : (T : Subgroup B).map B.subtype ≤ centralizer ({z} : Set G) := hT.symm ▸ hTz
  obtain ⟨hfusion,hclasses,hfour⟩ := source16_fusion_and_four_of_pair_rank_one
    h r ha hg hz hzM ht htM hu huD hzu htu hmax (hrank t ht htM) T hTM' huT'
  have hJ := source16_circle_centralizer_sylow_card_of_fusion h r ha hg hz hzM ht htM hu huD
    hzu htu hmax T huT' hTz' hfusion
  have hBM := residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  exact local_normalComplement_cyclicSylow_of_marked_outer h.disconnected r hu hBM
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩ hfour hclasses
    (fun P => le_of_eq (hJ P))
    (source16_circle_outer_sylow_cyclic h r ha hu huD.1 hBM hns)

/-- The exact source normalizer theorem used by Section 17, now with
Corollary 16.6(e) discharged and only Proposition 16.5 explicit. -/
public theorem source16_normalizer_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hrank : ∀ t ∈ Z, t ∉ M → ¬ TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    Section17.NativeSource.SectionSixteenNormalizer Z M :=
  Section16.NativeSource.sectionSixteenNormalizer_of_source h r ha
    (source16_local_complements_of_pair_rank_one h r ha hn hg hrank)

/-- The actual internal two-point stabilizer has an even normal-complement
quotient. This is the Section 16 input consumed after Proposition 17.6. -/
public theorem source16_pair_normal_complement_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hrank : ∀ t ∈ Z, t ∉ M → ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    {t : G} (htM : t ∉ M) :
    HasNormalPComplement 2 (residualPairIn M t) ∧ 2 ∣ Nat.card (residualPairIn M t) := by
  apply residualPairIn_normalComplement_of_local_cyclicSylow h.disconnected ha hn
    (fun Y hY => (source16_local_complements_of_pair_rank_one h r ha hn hg hrank Y hY).2) htM

end BenderSuzuki.ZD
