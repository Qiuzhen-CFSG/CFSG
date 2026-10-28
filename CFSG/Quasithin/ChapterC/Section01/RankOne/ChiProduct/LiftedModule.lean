module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CentralizerKernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
/-!
# Recognizing the actual lifted subgroup as a short block

A seed layer supported on a normal two-subgroup lies in the new core;
commutator generation then puts it in the new U-layer. Transport along
the literal inclusion K≤L carries the local displacement bound into L.
The preceding normal-generation and layer-dichotomy theorems prove
irreducibility. Support on V supplies elementary abelianness and
centrality in O₂(L), while the exact centralizer kernel identifies the
core quotient with the actual image selected by B.1.13.

This constructs every clause of IsBlock; no module-recognition or
irreducibility witness is assumed. Source: Aschbacher–Smith C.1.27,
printed p.133. The quotient image alternatives are the genuine earlier
B.1.13 conclusion, discharged by the model-selection producer.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem mapped_short_commutator (K : Subgroup G) (hK : IsShort K) :
    ⁅(blockU K).map K.subtype, K⁆ = (blockU K).map K.subtype := by
  have hh := commutator_isPPerfect_idempotent ⊤ (pCore 2 K)
    (hK.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
      (topEquiv (G := K)).symm.surjective) pCore_isPGroup le_normalizer_of_normal
  have hm := congrArg (Subgroup.map K.subtype) hh
  simpa only [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- The seed's layer lies in the new intrinsic U-layer as soon as its
support lies in a normal two-subgroup. -/
theorem seed_layer_le_lifted_layer
    (V K L : Subgroup G) [V.Normal] (hpV : IsPGroup 2 V)
    (hKL : K ≤ L) (hK : IsShort K) (hUV : (blockU K).map K.subtype ≤ V) :
    (blockU K).map K.subtype ≤ (blockU L).map L.subtype := by
  have hVL : V.comap L.subtype ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, hpV.comap_of_injective L.subtype L.subtype_injective⟩
  have hWU : (blockU K).map K.subtype ≤ (pCore 2 L).map L.subtype := by
    intro w hw
    refine ⟨⟨w, hKL (map_subtype_le _ hw)⟩, ?_, rfl⟩
    exact hVL (hUV hw)
  calc
    (blockU K).map K.subtype = ⁅(blockU K).map K.subtype, K⁆ :=
      (mapped_short_commutator K hK).symm
    _ ≤ ⁅(pCore 2 L).map L.subtype, L⁆ := commutator_mono hWU hKL
    _ = (blockU L).map L.subtype := by
      rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual inclusion K≤L transports both U-layers and the displacement
bound, giving the irreducible quotient of the lifted group. -/
theorem lifted_blockModuleIrreducible
    (V K L : Subgroup G) [V.Normal] (hpV : IsPGroup 2 V)
    (hKL : K ≤ L) (hK : IsShort K) (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hUKV : (blockU K).map K.subtype ≤ V)
    (hKQ : ⁅K, pCore 2 G⁆ ≤ (blockU K).map K.subtype)
    (hgen : conjugateSpanBy (K.subgroupOf L) ⊤ = ⊤) :
    BlockModuleIrreducible L := by
  let A := K.subgroupOf L
  let e : A ≃* K := subgroupOfEquivOfLe hKL
  have hA : IsShort A := hK.of_mulEquiv e.symm
  have hmA : A.map L.subtype = K := map_subgroupOf_eq_of_le hKL
  have hmU : ((blockU A).map A.subtype).map L.subtype = (blockU K).map K.subtype := by
    have he : L.subtype.comp A.subtype = K.subtype.comp e.toMonoidHom := rfl
    have hu : (blockU A).map e.toMonoidHom = blockU K := by
      rw [blockU, blockU, map_commutator, pCore_map_iso,
        map_top_of_surjective _ e.surjective]
    rw [map_map, he, ← map_map, hu]
  apply blockModuleIrreducible_of_short_seed A hA hpL hgen
  · apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hmU]
    exact seed_layer_le_lifted_layer V K L hpV hKL hK hUKV
  · apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_commutator, hmA, hmU]
    have hLQ : (blockU L).map L.subtype ≤ pCore 2 G :=
      (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL)
    exact (commutator_mono hLQ le_rfl).trans ((commutator_comm _ _).le.trans hKQ)

/-- The genuine B.1.13 image alternatives supply normal generation on the
literal centralizer quotient, so no irreducibility premise remains. -/
theorem lifted_blockModuleIrreducible_of_image
    (V K L : Subgroup G) [V.Normal] (hpV : IsPGroup 2 V)
    (hKL : K ≤ L) (hK : IsShort K) (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    (hUKV : (blockU K).map K.subtype ≤ V) (hULV : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G))
    (hKQ : ⁅K, pCore 2 G⁆ ≤ (blockU K).map K.subtype)
    (hi : let f := (QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L;
      (K.subgroupOf L).map f = ⊤ ∨ ⁅(K.subgroupOf L).map f, (⊤ : Subgroup (L.map (QuotientGroup.mk' (centralizer (V : Set G)))))⁆ = ⊤) :
    BlockModuleIrreducible L := by
  let f := (QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L
  have hk : IsPGroup 2 f.ker := by
    rw [core_eq_centralizer_quotient_kernel V L hL hfL hULV hQC]
    exact pCore_isPGroup
  have hg : conjugateSpanBy ((K.subgroupOf L).map f) ⊤ = ⊤ := by
    rcases hi with hi | hi
    · rw [hi]
      exact top_unique (le_conjugateSpanBy ⊤ ⊤)
    · exact conjugateSpan_eq_top_of_commutator_top _ hi
  have hn := normal_generation_of_twoGroup_kernel f
    ((QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap_surjective L)
    hk hpL (K.subgroupOf L) hg
  exact lifted_blockModuleIrreducible V K L hpV hKL hK hL hpL hUKV hKQ hn

open scoped IsMulCommutative in
private theorem elementary_of_embedding
    {A B : Type*} [Group A] [Group B] [IsElementaryAbelian 2 B]
    (f : A →* B) (hf : Function.Injective f) : IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply hf
    rw [map_mul, map_mul, mul_comm]
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply hf
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) (f a)

/-- The ambient lift is a genuine short block. The only model input is
the actual quotient image selected by B.1.13; irreducibility is proved. -/
theorem lifted_isBlock_of_image
    (V K L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hKL : K ≤ L) (hK : IsShort K) (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L)
    (hUKV : (blockU K).map K.subtype ≤ V) (hULV : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G))
    (hKQ : ⁅K, pCore 2 G⁆ ≤ (blockU K).map K.subtype)
    (hi : let f := (QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L;
      (K.subgroupOf L).map f = ⊤ ∨ ⁅(K.subgroupOf L).map f, (⊤ : Subgroup (L.map (QuotientGroup.mk' (centralizer (V : Set G)))))⁆ = ⊤)
    (hkind : IsQuasisimple (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) ∨
      Nat.card (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) = 3) : IsBlock L := by
  let i : blockU L →* V := (L.subtype.comp (blockU L).subtype).codRestrict V (by
    intro u
    exact hULV (mem_map_of_mem L.subtype u.property))
  have hi' : Function.Injective i := by
    intro a b he
    have hh : ((a : L) : G) = ((b : L) : G) :=
      congrArg (fun v : V => (v : G)) he
    exact Subtype.ext (Subtype.ext hh)
  refine ⟨inferInstance, ?_, hL⟩
  refine {
    finite := inferInstance
    twoPerfect := hpL
    fitting := hfL
    elementary := elementary_of_embedding i hi'
    central := ?_
    quotient := ?_
    irreducible := lifted_blockModuleIrreducible_of_image V K L
      (IsElementaryAbelian.isPGroup 2 V) hKL hK hL hpL hfL hUKV hULV hQC hKQ hi }
  · intro u hu q hq
    apply Subtype.ext
    exact (hQC (pCoreIn_le_of_subnormal 2 hL (mem_map_of_mem L.subtype hq))
      (u : G) (hULV (mem_map_of_mem L.subtype hu))).symm
  · let e := coreQuotientEquivCentralizerImage V L hL hfL hULV hQC
    rcases hkind with hkind | hkind
    · let := hkind
      exact Or.inl (IsQuasisimple.of_mulEquiv e.symm)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans hkind)

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
