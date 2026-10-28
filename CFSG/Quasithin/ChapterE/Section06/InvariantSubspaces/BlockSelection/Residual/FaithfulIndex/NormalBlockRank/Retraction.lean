module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.RankTransfer

/-!
# Rank reduction from an extended core-quotient map

A homomorphism that is bijective on a normal subgroup gives an internal
direct-product complement: its kernel commutes with the subgroup and maps
isomorphically onto the quotient. An element of order three in the normal
factor adds one to the quotient's three-rank.

The second theorem applies this after removing the characteristic two-core.
It requires an actual extension of the core-quotient map, from which the
splitting and every action-kernel comparison are derived.

Source: the A₃ case of the normal-block inference in Aschbacher--Smith,
combined manuscript (1 March 2004), proof of E.6.14, printed p.251,
using C.1.7--13, printed pp.123--125.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank

variable {G A : Type*} [Group G] [Finite G] [Group A]

/-- A homomorphism restricting to an isomorphism on a normal subgroup
constructs a commuting quotient section. -/
theorem rank_add_one_le_of_retraction (N : Subgroup G) [N.Normal]
    (f : G →* A) (hf : Function.Bijective (f.comp N.subtype))
    (x : N) (hx : orderOf x = 3) :
    primeRank 3 (G ⧸ N) + 1 ≤ primeRank 3 G := by
  let D := f.ker
  have hdis : Disjoint N D := by
    apply disjoint_def.mpr
    intro g hgN hgD
    have he : (⟨g, hgN⟩ : N) = 1 := hf.1 (show
      (f.comp N.subtype) ⟨g, hgN⟩ = (f.comp N.subtype) 1 from hgD.trans (map_one _).symm)
    exact congrArg Subtype.val he
  have hq : Function.Bijective ((QuotientGroup.mk' N).comp D.subtype) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff]
      apply bot_unique
      intro g hg
      have hgN : (g : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hg
      exact Subtype.ext (hdis.le_bot ⟨hgN, g.property⟩)
    · intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
      obtain ⟨n, hn⟩ := hf.2 (f g)
      have hmem : (n : G)⁻¹ * g ∈ D := by
        change f ((n : G)⁻¹ * g) = 1
        rw [map_mul, map_inv, show f (n : G) = f g from hn, inv_mul_cancel]
      refine ⟨⟨(n : G)⁻¹ * g, hmem⟩, ?_⟩
      change QuotientGroup.mk' N ((n : G)⁻¹ * g) = QuotientGroup.mk' N g
      have hnq : QuotientGroup.mk' N (n : G) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr n.property
      rw [map_mul, map_inv, hnq, inv_one, one_mul]
  have hc : D ≤ centralizer (N : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hdis.eq_bot]
    exact le_inf (commutator_le_right _ _) (commutator_le_left _ _)
  apply rank_add_one_le_of_centralizing_section N D hq x
    ((orderOf_injective N.subtype Subtype.val_injective x).trans hx)
  · intro hm
    have he : x = 1 := Subtype.ext (hdis.le_bot ⟨x.property, hm⟩)
    rw [he, orderOf_one] at hx
    omega
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hc hg) x x.property).symm)

/-- An extension of the core-quotient map suffices even when the block has a
nontrivial two-core. Splitting is proved after the coprime quotient. -/
theorem rank_add_one_le_of_core_retraction (N : Subgroup G) [N.Normal]
    (f : G →* (N ⧸ pCore 2 N))
    (hf : ∀ n : N, f (n : G) = QuotientGroup.mk' (pCore 2 N) n)
    (hcard : Nat.card (N ⧸ pCore 2 N) = 3) :
    primeRank 3 (G ⧸ N) + 1 ≤ primeRank 3 G := by
  let K : Subgroup G := (pCore 2 N).map N.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  let q := QuotientGroup.mk' K
  let R := N.map q
  let : R.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective K)
  have hK : K ≤ f.ker := by
    rintro g ⟨n, hn, rfl⟩
    change f (n : G) = 1
    rw [hf]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  let r := QuotientGroup.lift K f hK
  have hr : Function.Bijective (r.comp R.subtype) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff]
      apply bot_unique
      rintro ⟨y, hy⟩ h
      obtain ⟨g, hg, rfl⟩ := hy
      have hgK : (⟨g, hg⟩ : N) ∈ pCore 2 N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' (pCore 2 N) ⟨g, hg⟩ = 1
        rw [← hf]
        exact h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨g, hg⟩, hgK, rfl⟩
    · intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 N) y
      exact ⟨⟨q (n : G), mem_map_of_mem q n.property⟩, hf n⟩
  let e := MulEquiv.ofBijective (r.comp R.subtype) hr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card R by
    rw [Nat.card_congr e.toEquiv, hcard])
  have hh := rank_add_one_le_of_retraction R r hr x hx
  let eq : ((G ⧸ K) ⧸ R) ≃* G ⧸ N :=
    QuotientGroup.quotientQuotientEquivQuotient K N (Subgroup.map_subtype_le _)
  rw [primeRank_congr 3 eq] at hh
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    have hp : IsPGroup 2 K := (pCore_isPGroup (p := 2) (G := N)).map N.subtype
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact hh.trans (primeRank_quotient_le_of_coprime 3 K hcop)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank
