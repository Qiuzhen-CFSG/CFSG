module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.LocalGeometry.Source
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# The order-two outer action in the M₂₂ shadow

Full coverage by the design automorphisms bounds Out(M₂₂) by two. Descent
embeds the outer group of every perfect central cover in this same group;
there is no restriction to split covers. The actual outer action of R is
faithful once R₀ = 1. Its cardinality then proves R = ⟨r⟩.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed p.1186. The missing R₀ argument remains
explicit; this file does not assert R₀ = 1.
-/

public section

open Subgroup Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow

private theorem m22_outer_card_le_two : Nat.card (MulAut.Outer M22) ≤ 2 := by
  let N := M22.subgroupOf m22DesignAut
  let : N.Normal := M22_normal_in_m22DesignAut
  have hle : N ≤ (MulAut.innerSubgroup M22).comap m22DesignAutToAut := by
    intro g hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    rfl
  let q : (m22DesignAut ⧸ N) →* MulAut.Outer M22 :=
    QuotientGroup.map N (MulAut.innerSubgroup M22) m22DesignAutToAut hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M22) x
    obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective a
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have hc : Nat.card (m22DesignAut ⧸ N) = 2 := by
    rw [← N.index_eq_card]
    have heq : N = m22EvenDesignAut := by
      ext g
      simp [N, M22, m22EvenDesignAut]
    rw [heq, m22EvenDesignAut_index]
  exact hc ▸ Nat.card_le_card_of_surjective q hq

variable {G : Type*} [Group G]

private theorem cover_outer_card_le_two (L : Subgroup G) [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) : Nat.card (MulAut.Outer L) ≤ 2 :=
  (Nat.card_le_card_of_injective (MulAut.centralQuotientOuter e)
    (MulAut.centralQuotientOuter_injective e)).trans m22_outer_card_le_two

private theorem mem_product_of_inner (L : Subgroup G)
    (x : normalizer (L : Set G))
    (hx : L.normalizerMonoidHom x ∈ MulAut.innerSubgroup L) :
    (x : G) ∈ L ⊔ centralizer (L : Set G) := by
  obtain ⟨l, hl⟩ := hx
  let lN : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  have hlN : L.normalizerMonoidHom lN = MulAut.conj l := by
    ext y
    rfl
  have hc : lN⁻¹ * x ∈ L.normalizerMonoidHom.ker := by
    change L.normalizerMonoidHom (lN⁻¹ * x) = 1
    rw [map_mul, map_inv, hlN, hl, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hc
  have hm := (L ⊔ centralizer (L : Set G)).mul_mem
    ((show L ≤ L ⊔ centralizer (L : Set G) from le_sup_left) l.property)
    ((show centralizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) from le_sup_right) hc)
  simpa only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, lN, mul_inv_cancel_left] using hm

/-- A trivial inner part forces the given involution to generate R. The
outer bound is proved using the genuine M₂₂ automorphism coverage. -/
theorem eq_zpowers_of_innerPart_eq_bot [Finite G]
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (e : (L ⧸ center L) ≃* M22) (hinner : innerPart L R = ⊥) :
    R = zpowers r := by
  let := h.component.quasisimple
  let f : R →* MulAut.Outer L :=
    ((QuotientGroup.mk' (MulAut.innerSubgroup L)).comp L.normalizerMonoidHom).comp
      (inclusion (h.le_sylow.trans h.sylow_normalizes))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hi : L.normalizerMonoidHom
        (inclusion (h.le_sylow.trans h.sylow_normalizes) x) ∈ MulAut.innerSubgroup L :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hp := mem_product_of_inner L _ hi
    have hm : (x : G) ∈ innerPart L R := ⟨x.property, hp⟩
    have hx1 : (x : G) = 1 := by rwa [hinner, mem_bot] at hm
    exact Subtype.ext hx1
  have hc : Nat.card R ≤ 2 :=
    (Nat.card_le_card_of_injective f hf).trans (cover_outer_card_le_two L e)
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hr) ?_).symm
  simpa only [Nat.card_zpowers, hr2] using hc

/-- An outer element makes the bound sharp for any perfect M₂₂ cover. -/
theorem cover_outer_card_two_of_outer [Finite G] (L : Subgroup G) [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) (a : MulAut L) (ha : a ∉ MulAut.innerSubgroup L) :
    Nat.card (MulAut.Outer L) = 2 := by
  have hn : QuotientGroup.mk' (MulAut.innerSubgroup L) a ≠ 1 := by
    exact fun hh => ha ((QuotientGroup.eq_one_iff _).mp hh)
  let : Nontrivial (MulAut.Outer L) := nontrivial_iff.mpr ⟨_, 1, hn⟩
  exact Nat.le_antisymm (cover_outer_card_le_two L e)
    (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)

/-- The source C₄ obstruction with the outer order now supplied by the
actual central-quotient model and the proved automorphism coverage. The
commutator membership is the precise covering calculation still needed. -/
theorem center_card_ne_four_of_m22_outer_symmetry [Finite G]
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hsym : OuterFixedModel (L.conjBy g) z)
    (hQ : residualCore L r ≤ L.conjBy g)
    (hcover : Nat.card (center L) = 4 → z ∈ ⁅residualCore L r, residualCore L r⁆) :
    Nat.card (center L) ≠ 4 := by
  let := h.component.quasisimple
  let : Theory.GroupTheory.IsQuasisimple (L.conjBy g) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  apply center_card_ne_four_of_outer_symmetry L (L.conjBy g) r z
    hsym.normalizes hsym.outer
  · exact cover_outer_card_two_of_outer (L.conjBy g) hsym.quotientEquiv _ hsym.outer
  · exact hQ.trans (L.conjBy g).le_normalizer
  · exact hcover

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
