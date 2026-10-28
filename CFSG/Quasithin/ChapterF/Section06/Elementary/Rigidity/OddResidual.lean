module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Rigidity.Local
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Goldschmidt triples with odd two-residual

If O²(G) = O(G), each local residual centralizes its local two-core.
The intersection of the two cores is then normal in both generators and
vanishes when O₂(G) = 1. The two quotient maps on the common Sylow subgroup
have kernels of index two and trivial intersection. Their product embeds
it into C₂ × C₂, giving the genuine cyclic or Klein-four isomorphisms.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.14, printed p.307 (1 March 2004 manuscript).
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem core_centralizes_residual
    (hodd : pResidual 2 G = pPrimeCore 2 G) (M : Subgroup G) :
    (pCore 2 M).map M.subtype ≤ centralizer ((pResidual 2 M).map M.subtype : Set G) := by
  let Q := (pCore 2 M).map M.subtype
  let L := (pResidual 2 M).map M.subtype
  have hLO : L ≤ pPrimeCore 2 G := hodd ▸ map_pResidual_le 2 M.subtype
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map M.subtype
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card (pPrimeCore 2 G)) := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact pPrimeCore_coprime_card.pow_left n
  have hdis : Q ⊓ pPrimeCore 2 G = ⊥ := (disjoint_of_coprime_natCard hcop).eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  rw [← hdis]
  refine le_inf ?_ ((commutator_mono le_rfl hLO).trans (commutator_le_right _ _))
  change ⁅(pCore 2 M).map M.subtype, (pResidual 2 M).map M.subtype⁆ ≤ _
  rw [← map_commutator]
  exact map_mono (commutator_le_left _ _)

/-- The two local cores meet trivially when the ambient two-residual is odd
and the ambient two-core is trivial. -/
public theorem IsGoldschmidtTriple.core_intersection_trivial
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hodd : pResidual 2 G = pPrimeCore 2 G) :
    (pCore 2 G₁).map G₁.subtype ⊓ (pCore 2 G₂).map G₂.subtype = ⊥ := by
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  let N := Q₁ ⊓ Q₂
  have hNT : N ≤ G₁ ⊓ G₂ := inf_le_left.trans h.local_twoCore_le_intersection
  have hTN : G₁ ⊓ G₂ ≤ normalizer (N : Set G) :=
    (le_inf (inf_le_left.trans h.left_core_normalized)
      (inf_le_right.trans h.symm.left_core_normalized)).trans
        inf_normalizer_le_normalizer_inf
  have hc (M : Subgroup G) (hle : N ≤ (pCore 2 M).map M.subtype) :
      (pResidual 2 M).map M.subtype ≤ normalizer (N : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact le_centralizer_iff.mpr (hle.trans (core_centralizes_residual hodd M))
  apply h.common_normal_eq_bot hcore N hNT
  · apply (normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_left)).mpr
    rw [← h.left_residual_sup_intersection]
    exact sup_le (hc G₁ inf_le_left) hTN
  · apply (normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_right)).mpr
    rw [← h.right_residual_sup_intersection]
    exact sup_le (hc G₂ inf_le_right) hTN

private theorem equiv_c2 {H : Type*} [Group H] (hc : Nat.card H = 2) :
    Nonempty (H ≃* Multiplicative (ZMod 2)) :=
  ⟨mulEquivOfPrimeCardEq hc (by simp)⟩

/-- F.6.14, retaining O²(G) = O(G) and genuine isomorphisms of both local
cores in the Klein-four alternative. -/
public theorem IsGoldschmidtTriple.odd_residual_small_sylow
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hodd : pResidual 2 G = pPrimeCore 2 G) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∨
      (Nonempty ((pCore 2 G₁).map G₁.subtype ≃* Multiplicative (ZMod 2)) ∧
       Nonempty ((pCore 2 G₂).map G₂.subtype ≃* Multiplicative (ZMod 2)) ∧
       Nonempty (↥(G₁ ⊓ G₂) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  let T := G₁ ⊓ G₂
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  let K₁ := Q₁.subgroupOf T
  let K₂ := Q₂.subgroupOf T
  have hi₁ : K₁.index = 2 := h.left_core_index
  have hi₂ : K₂.index = 2 := by
    change Q₂.relIndex T = 2
    simpa only [inf_comm G₂ G₁] using h.symm.left_core_index
  let : K₁.Normal := normal_of_index_eq_two hi₁
  let : K₂.Normal := normal_of_index_eq_two hi₂
  have hmeet : K₁ ⊓ K₂ = ⊥ := by
    change (Q₁ ⊓ Q₂).comap T.subtype = ⊥
    rw [h.core_intersection_trivial hcore hodd]
    exact (MonoidHom.ker_eq_bot_iff T.subtype).mpr T.subtype_injective
  have hbound : Nat.card T ≤ 4 := by
    have hb := index_inf_le (H := K₁) (K := K₂)
    rw [hmeet, index_bot, hi₁, hi₂] at hb
    exact hb
  have hc₁ := K₁.index_mul_card
  have hc₂ := K₂.index_mul_card
  rw [hi₁] at hc₁
  rw [hi₂] at hc₂
  have htpos := Nat.card_pos (α := T)
  have hcases : Nat.card T = 2 ∨ Nat.card T = 4 := by omega
  rcases hcases with ht | ht
  · exact Or.inl (equiv_c2 ht)
  right
  have hq₁ : Nat.card Q₁ = 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
    change Nat.card K₁ = 2
    omega
  have hq₂ : Nat.card Q₂ = 2 := by
    have hle : Q₂ ≤ T := by
      simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
    rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    change Nat.card K₂ = 2
    omega
  refine ⟨equiv_c2 hq₁, equiv_c2 hq₂, ?_⟩
  let f := (QuotientGroup.mk' K₁).prod (QuotientGroup.mk' K₂)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk', hmeet]
  have hcard : Nat.card T = Nat.card ((T ⧸ K₁) × (T ⧸ K₂)) := by
    rw [Nat.card_prod, ← index_eq_card, ← index_eq_card, hi₁, hi₂, ht]
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)
  exact ⟨e.trans ((mulEquivOfPrimeCardEq (G' := Multiplicative (ZMod 2)) hi₁ (by simp)).prodCongr
    (mulEquivOfPrimeCardEq (G' := Multiplicative (ZMod 2)) hi₂ (by simp)))⟩
end CFSG.Quasithin.ChapterF
