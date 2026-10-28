module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts

/-!
# Reverse Δ₀ membership: ambient argument and final contradiction

The genuine Sylow upgrade is an explicit premise. Its transport and centralizer
isomorphism give reverse Δ membership. The contrary assumption, via 16.4.9(1),
forces |T_C|=2 and an outer involution on L′. Reversed 16.4.8 places the
actual two-residual L_z in L, and `Contracts` proves L_z ⊴ L_r.

The intrinsic comparison with the 16.1.4–5 tables remains a prerequisite:
`M12Comparison` must identify L/Z(L) with M₁₂ and the two residual images with
A₅. `M12LocalData` must then supply the covering lift, full inner centralizer,
and outer-centralizer action restriction. From those facts both contrary
branches are proved here. A nontrivial cover gives an order-four r_L and hence
an order-four r_C, impossible with |T_C|=2. In the centerless case the actual
C₂×S₅ centralizer has an outer actor on its A₅ subgroup, contradicting the
restriction in C_H′(z).

`reverse_deltaZero_of_model_inputs` is a conditional assembly theorem. This
module does not yet claim the source lemma with these two inputs discharged.
The Section04To05 owner also retains the earlier source inputs and the Sylow
premise. No two-core substitutes for a two-residual in this argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.11(2), printed pp.1193–1194.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Eliminate both M₁₂ branches after the genuine comparison and local rows have
been established. The nontrivial-cover branch is retained explicitly. -/
theorem contrary_impossible {r : G} (d : Contrary T z L g R r)
    (hS : SylowIn (commutingSylow T L) (centralizer (L : Set G)))
    (hc : M12Comparison L (L.conjBy g) r z)
    (hm : M12LocalData L (L.conjBy g) r z) : False := by
  have hZ : center L = ⊥ := by
    by_contra hn
    obtain ⟨c, hcK, l, hlL, hrl, hl4⟩ := hm.cover_lift hn
    have hcl : Commute c l := (show Commute l c from mem_centralizer_iff.mp hcK l hlL).symm
    have hc4 := cover_factor_order_four hcl d.involution hrl hl4
    exact no_order_four_of_sylow_card_two hS d.small hcK hc4
  have hZ' : center (L.conjBy g) = ⊥ := by
    apply (center (L.conjBy g)).eq_bot_iff_card.mpr
    calc
      Nat.card (center (L.conjBy g)) = Nat.card (center L) :=
        Nat.card_congr (Subgroup.centerCongr ((MulAut.conj g).subgroupMap L)).toEquiv.symm
      _ = 1 := (center L).eq_bot_iff_card.mp hZ
  obtain ⟨eC⟩ := hm.inner_centralizer hZ
  obtain ⟨eA⟩ := hc.outerResidual
  have hAC : residual (L.conjBy g) z ≤ L ⊓ centralizer ({r} : Set G) :=
    d.residual_normal.1.trans (residual_le L r)
  let f := (centralImageEquiv ((residual_le (L.conjBy g) z).trans inf_le_left) hZ').trans eA
  obtain ⟨x, hx, hout⟩ := product_has_outer_actor hAC eC f
  exact hout (hm.outer_restriction hZ x
    (inner_centralizer_le d.setup d.mem d.involution hx))

/-- The full reverse-Δ₀ deduction conditional on its two remaining intrinsic
inputs. Earlier 16.4.2, 16.4.8 and 16.4.9 inputs are stated individually.
Neither intrinsic input is proved by this theorem. -/
theorem reverse_deltaZero_of_model_inputs
    (h : IntersectionSetup T z L g R)
    (hET : HasEvenTypeCentralizers G)
    (hzero : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (ht : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hfaith : R ⊓ centralizer (L : Set G) = ⊥)
    (hnotnorm : ¬ L ≤ normalizer (L.conjBy g : Set G))
    (hsmall : ∀ J ∈ delta (L.conjBy g), J ∉ deltaZero (L.conjBy g) →
      ∀ S, SylowIn S (J ⊓ normalizer (centralizer (L.conjBy g : Set G) : Set G)) →
        Nat.card S = 2)
    (hreversed : z ∉ centralizer (L.conjBy g : Set G) ⊔ L.conjBy g →
      residual (L.conjBy g) z ≤ L)
    (hcompare : ∀ r, Contrary T z L g R r → M12Comparison L (L.conjBy g) r z)
    (hrows : ∀ r, Contrary T z L g R r → M12Comparison L (L.conjBy g) r z →
      M12LocalData L (L.conjBy g) r z) :
    centralizer (L : Set G) ∈ deltaZero (L.conjBy g) := by
  by_contra hnot
  obtain ⟨hcard, houter⟩ := contrary_small_outer h hR e ht hsmall hnot
  obtain ⟨_, ⟨eTC⟩, hn, _⟩ := centralizing_and_transport h hR e ht
  have hRcard : Nat.card R = 2 := (Nat.card_congr eTC.toEquiv).symm.trans hcard
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hRcard])
  have haG : orderOf (a : G) = 2 :=
    (orderOf_injective R.subtype R.subtype_injective a).trans ha
  have hzN : z ∈ normalizer (L.conjBy g : Set G) := by
    have hz := hn (z_mem_commutingSylow h)
    rwa [← centralizer_conjugate, normalizers_conjugate h.normalizers_eq] at hz
  let d : Contrary T z L g R a :=
    ⟨h, hET, hR, hzero, hfaith, hnotnorm, hcard, a.property, haG, hzN, houter,
      hreversed houter⟩
  exact contrary_impossible d (commuting_sylow h hR e ht)
    (hcompare a d) (hrows a d (hcompare a d))

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
