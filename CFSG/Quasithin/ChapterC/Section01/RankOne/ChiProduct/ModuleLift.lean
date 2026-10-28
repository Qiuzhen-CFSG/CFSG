module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CommutatorPreimage
/-!
# Propagating the short seed's irreducible moved layer

A short group's proper normal subgroups inside U are central: add the
fixed subgroup, apply irreducibility, and use [U,K]=U to remove the
fixed summand. Thus a normal two-layer whose K-displacement lies in U(K)
either contains U(K) or is centralized by K. Normal generation propagates
this dichotomy to the full moved layer and proves its central quotient
irreducible. No chief-series or semisimplicity assumption is added.

Source: the final noncentral-chief-factor argument of Aschbacher–Smith
C.1.27, printed p.133. The actual source lift supplies normal generation
through its two-core kernel and the local core-action displacement bound.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem short_commutator {K : Type*} [Group K] (h : IsShort K) :
    ⁅blockU K, (⊤ : Subgroup K)⁆ = blockU K := by
  let := h.finite
  exact commutator_isPPerfect_idempotent ⊤ (pCore 2 K)
    (h.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
      (topEquiv (G := K)).symm.surjective) pCore_isPGroup le_normalizer_of_normal

omit [Finite G] in
/-- A proper normal subgroup of the short moved layer is central. -/
theorem short_normal_layer_dichotomy (h : IsShort G) (N : Subgroup G) [N.Normal]
    (hNU : N ≤ blockU G) : N ≤ center G ∨ N = blockU G := by
  let C := blockU G ⊓ center G
  let D := N ⊔ C
  rcases h.irreducible.2 D inferInstance le_sup_right (sup_le hNU inf_le_left) with hd | hd
  · exact Or.inl ((le_sup_left.trans hd.le).trans inf_le_right)
  · right
    apply le_antisymm hNU
    have hCt : ⁅C, (⊤ : Subgroup G)⁆ = ⊥ :=
      commutator_top_right_eq_bot_iff_le_center.mpr inf_le_right
    have hD : D ≤ commutatorPreimage ⊤ ⊤ N :=
      sup_le (le_commutatorPreimage le_top (commutator_le_left _ _))
        (le_commutatorPreimage le_top (hCt.le.trans bot_le))
    have hc := (commutator_mono hD le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ ⊤ N le_normalizer_of_normal)
    rwa [hd, short_commutator h] at hc

/-- A normal two-subgroup either contains the whole short moved layer or
is centralized by the short seed, when its displacement lies in that layer. -/
theorem normal_two_layer_short_dichotomy
    (K N : Subgroup G) (hK : IsShort K) [N.Normal] (hpN : IsPGroup 2 N)
    (hcomm : ⁅N, K⁆ ≤ (blockU K).map K.subtype) :
    (blockU K).map K.subtype ≤ N ∨ K ≤ centralizer (N : Set G) := by
  let A := ⁅N, K⁆
  have hAK : A ≤ K := hcomm.trans (map_subtype_le _)
  let : (A.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right N K)
  have hAU : A.subgroupOf K ≤ blockU K := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hcomm hx
    exact (Subtype.ext he : y = x) ▸ hy
  rcases short_normal_layer_dichotomy hK (A.subgroupOf K) hAU with hc | he
  · right
    have hAC : A ≤ centralizer (K : Set G) := by
      intro a ha k hk
      exact congrArg Subtype.val (mem_center_iff.mp (hc (show (⟨a, hAK ha⟩ : K) ∈ A.subgroupOf K from ha)) ⟨k, hk⟩)
    have hzero : ⁅A, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hAC
    have hid := commutator_isPPerfect_idempotent K N hK.twoPerfect hpN
      le_normalizer_of_normal
    have hb : A = ⊥ := hid.symm.trans hzero
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
  · left
    have hh := congrArg (Subgroup.map K.subtype) he
    rw [map_subgroupOf_eq_of_le hAK] at hh
    exact hh.symm.le.trans (commutator_le_left N K)

/-- Normal generation by one short seed propagates its single noncentral
layer to the whole moved elementary module. -/
theorem normal_layer_dichotomy_of_short_seed
    (K V : Subgroup G) (hK : IsShort K) [V.Normal] (hpV : IsPGroup 2 V)
    (hgen : conjugateSpanBy K ⊤ = ⊤) (hwhole : ⁅V, (⊤ : Subgroup G)⁆ = V)
    (hcomm : ⁅V, K⁆ ≤ (blockU K).map K.subtype)
    (N : Subgroup G) [N.Normal] (hNV : N ≤ V) :
    N ≤ center G ∨ N = V := by
  rcases normal_two_layer_short_dichotomy K N hK (hpV.to_le hNV)
    ((commutator_mono hNV le_rfl).trans hcomm) with hu | hc
  · right
    apply le_antisymm hNV
    let D := commutatorPreimage ⊤ V N
    have hDN : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
      (commutatorPreimage_normalized ⊤ V N ⊤ le_normalizer_of_normal
        le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal))
    let := hDN
    have hKD : K ≤ D := le_commutatorPreimage le_top (by
      rw [commutator_comm]
      exact hcomm.trans hu)
    have htop : (⊤ : Subgroup G) ≤ D := hgen ▸
      (conjugateSpanBy_le hKD le_normalizer_of_normal)
    have hh := (commutator_mono htop (show V ≤ V from le_rfl)).trans
      (commutator_commutatorPreimage_le ⊤ V N le_normalizer_of_normal)
    rwa [commutator_comm, hwhole] at hh
  · left
    have htop : (⊤ : Subgroup G) ≤ centralizer (N : Set G) := hgen ▸
      (conjugateSpanBy_le hc le_normalizer_of_normal)
    exact commutator_top_right_eq_bot_iff_le_center.mp
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp htop))


/-- The actual intrinsic U/C_U(G) is irreducible once G is normally
generated by the short seed and the seed accounts for its displacement. -/
theorem blockModuleIrreducible_of_short_seed
    (K : Subgroup G) (hK : IsShort K) (hpG : IsPPerfect 2 G)
    (hgen : conjugateSpanBy K ⊤ = ⊤)
    (hUK : (blockU K).map K.subtype ≤ blockU G)
    (hcomm : ⁅blockU G, K⁆ ≤ (blockU K).map K.subtype) :
    BlockModuleIrreducible G := by
  have hwhole : ⁅blockU G, (⊤ : Subgroup G)⁆ = blockU G :=
    commutator_isPPerfect_idempotent ⊤ (pCore 2 G)
      (hpG.of_surjective (topEquiv (G := G)).symm.toMonoidHom
        (topEquiv (G := G)).symm.surjective) pCore_isPGroup le_normalizer_of_normal
  have hne : blockU G ≠ ⊥ := by
    intro he
    have hb : (blockU K).map K.subtype = ⊥ := bot_unique (he ▸ hUK)
    exact hK.blockU_ne_bot (((blockU K).map_eq_bot_iff_of_injective K.subtype_injective).mp hb)
  refine ⟨lt_of_le_of_ne inf_le_left ?_, ?_⟩
  · intro he
    have hc : blockU G ≤ center G := he.symm.le.trans inf_le_right
    exact hne (hwhole.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hc))
  · intro N hn hCN hNU
    let := hn
    rcases normal_layer_dichotomy_of_short_seed K (blockU G) hK
      (pCore_isPGroup.to_le blockU_le_core) hgen hwhole hcomm N hNU with hc | he
    · exact Or.inl (le_antisymm (le_inf hNU hc) hCN)
    · exact Or.inr he

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
