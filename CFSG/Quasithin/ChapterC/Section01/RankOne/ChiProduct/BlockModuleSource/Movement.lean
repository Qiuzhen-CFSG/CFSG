module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimpleQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient

/-!
# Thompson movement of the actual ambient χ-block

The original J(T) normalizes its moved short seed. It therefore normalizes
any ambient block containing that seed: otherwise guarded block commutation
would make the seed abelian. In a χ-block the simple two-core quotient and
two-perfection show that every normal subgroup containing the seed is the
whole block. Apply this to [L,J(T)].

Source: Aschbacher--Smith C.1.28, printed pp.133--134.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource

private theorem chi_simple_quotient {L : Type*} [Group L] (h : IsChiBlock L) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  rcases h with h | ⟨n,hn,ha⟩
  · exact IsChiZeroBlock.simple_quotient (Or.inl h)
  · by_cases h3 : n = 3
    · subst n
      exact IsChiZeroBlock.simple_quotient (Or.inr (Or.inl ha))
    · obtain ⟨e⟩ := ha.2.2.quotient_iso
      have hn5 : 5 ≤ n := by have hh := ha.1; obtain ⟨k,hk⟩ := hn; omega
      let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
      exact e.isSimpleGroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem short_noncommuting (K : Subgroup G) (hK : IsShort K) : ⁅K,K⁆ ≠ ⊥ := by
  intro hh
  have hu : (blockU K).map K.subtype ≤ ⁅K,K⁆ := by
    rw [blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    exact commutator_mono (map_subtype_le _) le_rfl
  rw [hh] at hu
  exact hK.blockU_ne_bot (((blockU K).map_eq_bot_iff_of_injective K.subtype_injective).mp (bot_unique hu))

/-- A block containing a normalized short seed is normalized by the same
actor: a distinct conjugate block would centralize the nonabelian seed. -/
theorem normalizes_block_of_short_seed
    (hf : generalizedFitting G = pCore 2 G)
    (K L J : Subgroup G) (hK : IsShort K) (hL : IsBlock L)
    (hKL : K ≤ L) (hJK : J ≤ normalizer K) : J ≤ normalizer L := by
  intro j hj
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hb := hL.map_equiv (MulAut.conj j)
  have hc := blocks_commute (blockCommutationHypothesis_of_fitting hf) hb hL he
  have hfix : K.map (MulAut.conj j).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (hJK hj)
  have hKm : K ≤ L.map (MulAut.conj j).toMonoidHom :=
    hfix ▸ map_mono hKL
  exact short_noncommuting K hK (bot_unique ((commutator_mono hKm hKL).trans hc.le))

/-- In a χ-block, every normal subgroup containing a short seed is the whole
block. The simple two-core quotient and two-perfection exclude both proper cases. -/
theorem normal_subgroup_eq_top_of_short_seed
    {L : Type*} [Group L] (hL : IsChiBlock L)
    (K N : Subgroup L) (hK : IsShort K) [N.Normal] (hKN : K ≤ N) : N = ⊤ := by
  let : Finite L := hL.short.finite
  let : IsSimpleGroup (L ⧸ pCore 2 L) := chi_simple_quotient hL
  let q := QuotientGroup.mk' (pCore 2 L)
  have hn : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hNQ : N ≤ pCore 2 L := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hb
    have hp : IsPGroup 2 K := pCore_isPGroup.to_le (hKN.trans hNQ)
    have he := hK.twoPerfect (⊥ : Subgroup K) inferInstance
      (hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
    have hu : blockU K = ⊥ := by
      apply bot_unique
      rw [he]
      exact le_top
    exact (hK.blockU_ne_bot hu).elim
  · have hsup : N ⊔ pCore 2 L = ⊤ := by
      rw [← QuotientGroup.ker_mk' (pCore 2 L), ← comap_map_eq, ht, comap_top]
    exact hL.short.twoPerfect N inferInstance
      (isPGroup_quotient_of_sup_eq_top N (pCore 2 L) pCore_isPGroup hsup)

/-- The original Thompson movement passes from the local seed to its
ambient χ-block, without a normal-generation or module-action premise. -/
theorem block_moved_of_short_seed
    (hf : generalizedFitting G = pCore 2 G)
    (K L J : Subgroup G) (hK : IsShort K) (hL : IsChiBlockIn L)
    (hKL : K ≤ L) (hmove : K = ⁅K,J⁆) : L = ⁅L,J⁆ := by
  have hJK : J ≤ normalizer K :=
    le_normalizer_iff_commutator_le_left.mpr hmove.ge
  have hJL := normalizes_block_of_short_seed hf K L J hK hL.1 hKL hJK
  have hcL : ⁅L,J⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hJL
  let N := (⁅L,J⁆).subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left L J)
  let A := K.subgroupOf L
  have hA : IsShort A := hK.of_mulEquiv (subgroupOfEquivOfLe hKL).symm
  have hAN : A ≤ N := fun _ hk =>
    (hmove.le.trans (commutator_mono hKL le_rfl)) hk
  have he := normal_subgroup_eq_top_of_short_seed hL.2 A N hA hAN
  have hm := congrArg (map L.subtype) he
  rw [map_subgroupOf_eq_of_le hcL,← MonoidHom.range_eq_map,range_subtype] at hm
  exact hm.symm

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
