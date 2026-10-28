module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# A short local seed generates the original block

A short subgroup normalized by the ambient two-core has its moved layer in
Ω₁Z(O₂(G)): mutual normalization gives core centrality, and characteristic
two puts the layer inside the core. Its external core displacement lies in
that layer. Normal generation therefore puts the whole intrinsic moved
layer in the same elementary central subgroup. The short seed's normal-layer
dichotomy proves irreducibility. A noncentral image in the quasisimple core
quotient supplies normal generation through the two-group kernel.

The final theorem applies this proof through the literal inclusion K ≤ L.
Source: Aschbacher–Smith C.1.21, block-propagation paragraph, printed p.128.
The imported ModuleLift proof is the same elementary normal-layer argument;
no later C.1.27 or C.1.28 source conclusion is invoked.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
variable {G : Type*} [Group G] [Finite G]

private theorem short_seed_core_commutator (K : Subgroup G) (hK : IsShort K)
    (hQK : pCore 2 G ≤ normalizer (K : Set G)) :
    ⁅pCore 2 G, K⁆ ≤ (blockU K).map K.subtype := by
  have hcomm : ⁅pCore 2 G, K⁆ ≤ pCoreIn 2 K :=
    le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le (le_normalizer_iff_commutator_le_left.mp
        (show K ≤ normalizer (pCore 2 G : Set G) from le_normalizer_of_normal)))
      (le_normalizer_iff_commutator_le_right.mp hQK)
      (normalizer_commutator_ge_right (pCore 2 G) K)
  have hi := commutator_isPPerfect_idempotent K (pCore 2 G) hK.twoPerfect
    pCore_isPGroup le_normalizer_of_normal
  rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact hi.symm.le.trans (commutator_mono hcomm le_rfl)

private theorem seed_layer_le_core_layer (K : Subgroup G) (hK : IsShort K)
    (hUQ : (blockU K).map K.subtype ≤ pCore 2 G) :
    (blockU K).map K.subtype ≤ blockU G := by
  have hi := commutator_isPPerfect_idempotent ⊤ (pCore 2 K)
    (hK.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
      (topEquiv (G := K)).symm.surjective) pCore_isPGroup le_normalizer_of_normal
  have hh := congrArg (Subgroup.map K.subtype) hi
  have he : ⁅(blockU K).map K.subtype, K⁆ = (blockU K).map K.subtype := by
    simpa only [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact he.symm.le.trans (commutator_mono hUQ le_top)

/-- Normal generation by a core-normalized short seed makes the group short. -/
theorem isShort_of_normal_generation (K : Subgroup G) (hK : IsShort K)
    (hp : IsPPerfect 2 G) (hf : generalizedFitting G = pCore 2 G)
    (hq : IsQuasisimple (G ⧸ pCore 2 G) ∨ Nat.card (G ⧸ pCore 2 G) = 3)
    (hQK : pCore 2 G ≤ normalizer (K : Set G))
    (hgen : conjugateSpanBy K ⊤ = ⊤) : IsShort G := by
  let W := omegaCenterIn (pCore 2 G)
  have hWN : W.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
    ((show (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G) from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_omegaCenterIn _)))
  let := hWN
  have hUC : (blockU K).map K.subtype ≤ centralizer (pCore 2 G : Set G) :=
    le_centralizer_iff.mp (hK.normalizing_twoGroup_centralizes_blockU
      pCore_isPGroup le_normalizer_of_normal hQK)
  have hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hf]
    exact centralizer_generalizedFitting_le G
  have hUW : (blockU K).map K.subtype ≤ W := by
    let : IsElementaryAbelian 2 ((blockU K).map K.subtype) := hK.elementary.map K.subtype
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hself (hUC hx),hUC hx,elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hcomm := short_seed_core_commutator K hK hQK
  let D := commutatorPreimage ⊤ (pCore 2 G) W
  have hDN : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
    (commutatorPreimage_normalized ⊤ (pCore 2 G) W ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal))
  let := hDN
  have hKD : K ≤ D := le_commutatorPreimage le_top
    ((commutator_comm _ _).le.trans (hcomm.trans hUW))
  have htop : (⊤ : Subgroup G) ≤ D := hgen ▸ conjugateSpanBy_le hKD le_normalizer_of_normal
  have hUG : blockU G ≤ W := by
    change ⁅pCore 2 G, ⊤⁆ ≤ W
    rw [commutator_comm]
    exact (commutator_mono htop le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ (pCore 2 G) W le_normalizer_of_normal)
  refine {
    finite := inferInstance
    twoPerfect := hp
    fitting := hf
    elementary := IsElementaryAbelian.of_injective (inclusion hUG) (inclusion_injective hUG)
    central := ?_
    quotient := hq
    irreducible := ChiProduct.blockModuleIrreducible_of_short_seed K hK hp hgen
      (seed_layer_le_core_layer K hK (hUC.trans hself))
      ((commutator_mono blockU_le_core le_rfl).trans hcomm) }
  intro x hx
  exact ((mem_omegaCenterIn_iff _ _).mp (hUG hx)).2.1

omit [Finite G] in
/-- A noncentral seed normally generates a two-perfect group with quasisimple core quotient. -/
theorem normal_generation_of_noncentral_core_image (K : Subgroup G)
    (hp : IsPPerfect 2 G) [IsQuasisimple (G ⧸ pCore 2 G)]
    (hne : ¬ K.map (QuotientGroup.mk' (pCore 2 G)) ≤ center (G ⧸ pCore 2 G)) :
    conjugateSpanBy K ⊤ = ⊤ := by
  let N := conjugateSpanBy K ⊤
  let : N.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (le_normalizer_conjugateSpanBy K ⊤))
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (N.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hm : N.map q = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hc | he
    · exact (hne ((map_mono (le_conjugateSpanBy K ⊤)).trans hc)).elim
    · exact he
  have hs : N ⊔ pCore 2 G = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  have hn : pResidual 2 G ≤ N :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N (pCore 2 G) pCore_isPGroup hs⟩
  rw [(pResidual_eq_top_iff 2 G).mpr hp] at hn
  exact top_unique hn

/-- The actual subgroup inclusion propagates the selected local short block to L. -/
theorem isBlock_of_short_seed (K L : Subgroup G) (hKL : K ≤ L)
    (hK : IsShort K) (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hQK : pCore 2 G ≤ normalizer (K : Set G))
    (hne : ¬ (K.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤
      center (L ⧸ pCore 2 L)) : IsBlock L := by
  let A := K.subgroupOf L
  have hA : IsShort A := hK.of_mulEquiv (subgroupOfEquivOfLe hKL).symm
  have hQA : pCore 2 L ≤ normalizer (A : Set L) := by
    apply le_normalizer_iff.mpr
    intro q hq x hx
    exact le_normalizer_iff.mp hQK q
      (pCoreIn_le_of_subnormal 2 hL (mem_map_of_mem L.subtype hq)) x hx
  exact ⟨inferInstance, isShort_of_normal_generation A hA hpL hfL
    (Or.inl inferInstance) hQA (normal_generation_of_noncentral_core_image A hpL hne),hL⟩
end CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
