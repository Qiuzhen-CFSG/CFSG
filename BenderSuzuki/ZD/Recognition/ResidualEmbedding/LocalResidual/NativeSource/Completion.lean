module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NativeSource
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.RankBound

/-!
# Completion of the local residual argument

The original-input pair-rank proposition supplies the sole remaining
Section 16 hypothesis of the completed Section 17 consumer. The resulting
complement and normal two-complement quotient make the two-residual of M
proper. Action and generation are precisely the earlier source conclusions
and are discharged by the final residual assembly.

Source: GLS IV, Chapter 2, Sections 16–17 and Proposition 17.6.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- Corollary 16.6(e) on the original source hypotheses. -/
public theorem local_normal_complements_of_residualGeneration
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M) :
    ∀ Y : Subgroup G, localCircle Z Y=⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S :=
  source16_local_complements_of_pair_rank_one h r ha hn hg
    (fun _ ht htM => source16_pair_not_twoRank h r ha hg hn ht htM)

/-- The literal internal pair stabilizer has an even normal two-complement
quotient, with Proposition 16.5 and all selected data discharged. -/
public theorem residualPair_normal_complement_of_residualGeneration
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    {t : G} (htM : t∉M) :
    HasNormalPComplement 2 (residualPairIn M t) ∧ 2∣Nat.card (residualPairIn M t) :=
  source16_pair_normal_complement_of_pair_rank_one h r ha hn hg
    (fun _ ht htM => source16_pair_not_twoRank h r ha hg hn ht htM) htM

/-- Proposition 17.6's actual complement inside M. Every selected
configuration, rank, local normalizer, fusion and counting input is constructed. -/
public theorem exists_twoCore_complement_of_residualGeneration
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M) :
    ∃ t∈Z, t∉M ∧ (residualPairIn M t).IsComplement' (pCore 2 M) := by
  have hrank : ∀ t∈Z, t∉M → ¬TwoRankAtLeastTwo (residualPairStabilizer M t) :=
    fun _ ht htM => source16_pair_not_twoRank h r ha hg hn ht htM
  have hlocal := source16_local_complements_of_pair_rank_one h r ha hn hg hrank
  have h16 := source16_normalizer_of_pair_rank_one h r ha hn hg hrank
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
  have hzT' : z ∈ (T : Subgroup B).map B.subtype := hT.symm ▸ hzT
  have hTz' : (T : Subgroup B).map B.subtype ≤ centralizer ({z} : Set G) := hT.symm ▸ hTz
  obtain ⟨hfusion,hclasses,_⟩ := source16_fusion_and_four_of_pair_rank_one
    h r ha hg hz hzM ht htM hu huD hzu htu hmax (hrank t ht htM) T hTM' huT'
  have hcentral : ∃ SD : Sylow 2 (residualPairStabilizer M t),
      (SD : Subgroup (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype ≤ B := by
    let D := residualPairStabilizer M t
    let uD : D := ⟨u,huD⟩
    have hui : PFAppendixIII.IsInvolution uD := IsInvolution.subtype hu huD
    obtain ⟨SD,hSD⟩ := (isPGroup_zpowers_of_involution hui).exists_le_sylow
    let : IsCyclic SD := (hlocal D (residualPairStabilizer_localClosure_eq_bot h.disconnected htM)).2 SD
    let : CommGroup SD := IsCyclic.commGroup
    refine ⟨SD,?_⟩
    rintro x ⟨v,hv,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun y : SD => ((y : D) : G))
      (mul_comm (⟨v,hv⟩ : SD) ⟨uD,hSD (mem_zpowers uD)⟩)
  obtain ⟨P,hdiv⟩ := source17_trace_divisor_of_selected_source h r ha ht htM hu huD htu hz
    T hTM' huT' hzT' hTz' hcentral hfusion
  have hti := h.disconnected.involutions t ht
  have htuI : PFAppendixIII.IsInvolution (t * u) := by
    refine ⟨?_,?_⟩
    · intro he
      exact htM ((mul_eq_one_iff_eq_inv.mp he).trans hu.inv_eq_self ▸ huD.1)
    · rw [htu.mul_pow,hti.sq_eq_one,hu.sq_eq_one,mul_one]
  have htuZ : t * u ∉ Z := by
    intro hmem
    have hprod : (t * u) * t = u := by
      rw [htu.eq,mul_assoc,← pow_two,hti.sq_eq_one,mul_one]
    have hC : centralizer ({u} : Set G) ≤ M := by
      simpa only [hprod] using h.disconnected.product_centralizer (t*u) hmem t ht
        (hprod.symm ▸ hu) (hprod.symm ▸ huD.1)
    exact htM (hC (mem_centralizer_singleton_iff.mpr htu.eq))
  have hfusion' : IsConj u (t*u) := (hclasses (t*u) htuI).resolve_left htuZ
  let uD : residualPairIn M t := ⟨⟨u,huD.1⟩,huD⟩
  have huD2 : orderOf uD = 2 := by
    simpa only [Subgroup.orderOf_coe] using
      (show orderOf ((uD : M) : G) = 2 from orderOf_eq_prime hu.sq_eq_one hu.ne_one)
  obtain ⟨t',ht',ht'M,hsplit⟩ := Section17.NativeSource.exists_twoCore_complement_of_selected_source
    h r ha hn hg hlocal h16 t ht htM uD huD2 htu ⟨z,hzM⟩ hz hzu hfusion'
    (source16_centralizer_nonsolvable h r ha ht htM hu huD) P hdiv
  exact ⟨t',ht',ht'M,hsplit⟩

/-- The complete local analysis, with no model, rank, fusion, counting or
splitting premise beyond the original earlier action and generation theorems. -/
public theorem twoResidual_ne_top_of_residualGeneration
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M) :
    External.hallPResidual 2 M ≠ ⊤ :=
  by
    obtain ⟨t,_,htM,hsplit⟩ := exists_twoCore_complement_of_residualGeneration h r ha hn hg
    obtain ⟨hcomp,heven⟩ := residualPair_normal_complement_of_residualGeneration h r ha hn hg htM
    exact twoResidual_ne_top_of_split_pair hsplit hcomp heven

end BenderSuzuki.ZD
