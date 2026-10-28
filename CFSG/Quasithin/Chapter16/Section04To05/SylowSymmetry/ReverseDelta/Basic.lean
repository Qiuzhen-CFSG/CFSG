module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Consequences
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The ambient part of reverse Δ₀ membership

After the explicit Sylow upgrade, conjugation transports R back to T_C.
This makes T_C Sylow in the reverse relative normalizer and proves reverse
Δ membership. Failure of Δ₀, using 16.4.9(1), forces |T_C|=2 and makes z
outer on L′. The reversed residual placement gives L_z ⊴ L_r and, more
strongly, normalization of L_z by C_L(r). The cover calculation preserves
the order-four centralizer factor and rules it out using the Sylow order.

These are ambient deductions, not the missing inner/outer centralizer-table
comparison. Residuals throughout are O², and normality is relative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.11(2), printed pp.1193–1194.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The embedded two-residual O²(C_L(t)). -/
def residual (L : Subgroup G) (t : G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer ({t} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({t} : Set G)).subtype

theorem residual_le (L : Subgroup G) (t : G) :
    residual L t ≤ L ⊓ centralizer ({t} : Set G) := map_subtype_le _

theorem centralizer_conjugate (L : Subgroup G) (g : G) :
    centralizer (L.conjBy g : Set G) = (centralizer (L : Set G)).conjBy g := by
  exact (map_centralizer_equiv (L : Set G) (MulAut.conj g)).symm

theorem normalizers_conjugate {L : Subgroup G} {g : G}
    (he : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G)) :
    normalizer (centralizer (L.conjBy g : Set G) : Set G) =
      normalizer (L.conjBy g : Set G) := by
  rw [centralizer_conjugate]
  change normalizer (Subgroup.map (MulAut.conj g).toMonoidHom _ : Set G) =
    normalizer (Subgroup.map (MulAut.conj g).toMonoidHom _ : Set G)
  rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq, he]

variable [Finite G]

private theorem sylow_map {R H : Subgroup G} (h : SylowIn R H) (e : G ≃* G) :
    SylowIn (R.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  obtain ⟨S, rfl⟩ := h
  let f := e.subgroupMap H
  refine ⟨Sylow.mapSurjective (f := f.toMonoidHom) f.surjective S, ?_⟩
  change ((S : Subgroup H).map f.toMonoidHom).map _ = _
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨f w, ⟨w, hw, rfl⟩, rfl⟩

private theorem sylow_restrict {R H J : Subgroup G} (h : SylowIn R H)
    (hRJ : R ≤ J) (hJH : J ≤ H) : SylowIn R J := by
  obtain ⟨S, hS⟩ := h
  have hSJ : (S : Subgroup H) ≤ J.subgroupOf H := by
    intro x hx
    exact hRJ (hS ▸ (mem_map.mpr ⟨x, hx, rfl⟩))
  let P := S.subtype hSJ
  let e := subgroupOfEquivOfLe hJH
  refine ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P, ?_⟩
  change (((S : Subgroup H).subgroupOf (J.subgroupOf H)).map e.toMonoidHom).map J.subtype = R
  apply le_antisymm
  · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact hS ▸ (mem_map.mpr ⟨w.val, hw, rfl⟩)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp (hS.symm ▸ hx)
    refine ⟨⟨y, hSJ hy⟩, ?_, rfl⟩
    exact ⟨⟨y, hSJ hy⟩, hy, rfl⟩

/-- A Sylow two-subgroup of order two rules out elements of order four
in its full overgroup. -/
theorem no_order_four_of_sylow_card_two {C K : Subgroup G}
    (hS : SylowIn C K) (hC : Nat.card C = 2) {c : G} (hc : c ∈ K) :
    orderOf c ≠ 4 := by
  obtain ⟨S, rfl⟩ := hS
  have hScard : Nat.card S = 2 := by
    rwa [card_map_of_injective K.subtype_injective] at hC
  intro h4
  have h4K : orderOf (⟨c, hc⟩ : K) = 4 :=
    (orderOf_injective K.subtype K.subtype_injective _).symm.trans h4
  have hd : 2 ^ 2 ∣ Nat.card K := by
    simpa only [h4K, show 2 ^ 2 = 4 from rfl] using orderOf_dvd_natCard (⟨c, hc⟩ : K)
  have hh := S.pow_dvd_card_of_pow_dvd_card hd
  rw [hScard] at hh
  norm_num at hh

set_option backward.isDefEq.respectTransparency false in
private theorem omega_le_of_sylow {R Q H D : Subgroup G}
    (hR : SylowIn R H) (hQ : SylowIn Q H)
    (hD : H ≤ normalizer (D : Set G)) (hOmega : omegaOneAmbient Q ≤ D) :
    omegaOneAmbient R ≤ D := by
  obtain ⟨P, rfl⟩ := hR
  obtain ⟨S, rfl⟩ := hQ
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H S P
  have he : (S : Subgroup H).map (MulAut.conj a).toMonoidHom = (P : Subgroup H) :=
    congrArg (fun P : Sylow 2 H => (P : Subgroup H)) ha
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro r hr hr2
  obtain ⟨p, hp, rfl⟩ := hr
  obtain ⟨q, hq, hqp⟩ := mem_map.mp (he.symm ▸ hp)
  change MulAut.conj a q = p at hqp
  have hq2 : (q : G) ^ 2 = 1 := by
    have hp2 : p ^ 2 = 1 := Subtype.ext hr2
    have hqH : q ^ 2 = 1 := by
      apply (MulAut.conj a).injective
      simpa only [map_pow, map_one, hqp] using hp2
    exact congrArg Subtype.val hqH
  have hqD : (q : G) ∈ D := (omegaOneAmbient_le_iff _ _).mp hOmega q
    ⟨q, hq, rfl⟩ hq2
  have hconj := (mem_normalizer_iff.mp (hD a.property) q).mp hqD
  have heG : (a : G) * q * (a : G)⁻¹ = (p : G) := congrArg Subtype.val hqp
  change (p : G) ∈ D
  rw [← heG]
  exact hconj

variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

theorem z_mem_commutingSylow (h : IntersectionSetup T z L g R) :
    z ∈ commutingSylow T L := by
  refine ⟨h.mem_sylow, mem_centralizer_iff.mpr ?_⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mp (h.component.1 hx)

/-- The Δ₀ omega condition holds for the chosen relative Sylow R,
not just for the existential Sylow in the definition. -/
theorem omega_le_of_deltaZero (h : IntersectionSetup T z L g R)
    (hzero : (centralizer (L : Set G)).conjBy g ∈ deltaZero L) :
    omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L := by
  obtain ⟨_, Q, hQ, hOmega⟩ := hzero
  apply omega_le_of_sylow h.sylow hQ _ hOmega
  apply inf_le_right.trans
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_inf le_rfl (le_of_eq h.normalizers_eq)

/-- Reverse relative Sylow membership, after the explicit Sylow upgrade. -/
theorem commuting_sylow (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (ht : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    SylowIn (commutingSylow T L) (centralizer (L : Set G)) := by
  obtain ⟨_, _, _, he⟩ := centralizing_and_transport h hR e ht
  have hs := sylow_map hR (MulAut.conj g⁻¹)
  change SylowIn (R.conjBy g⁻¹)
    (((centralizer (L : Set G)).conjBy g).conjBy g⁻¹) at hs
  rw [he, conjBy_inv, conjBy_inv] at hs
  exact hs

/-- T_C is Sylow in the reverse relative normalizer as well. -/
theorem reverse_sylow (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (ht : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    SylowIn (commutingSylow T L)
      (centralizer (L : Set G) ⊓ normalizer (centralizer (L.conjBy g : Set G) : Set G)) := by
  have hn := (centralizing_and_transport h hR e ht).2.2.1
  apply sylow_restrict (commuting_sylow h hR e ht)
  · exact le_inf inf_le_right (by rwa [centralizer_conjugate])
  · exact inf_le_left

/-- Reverse Δ membership is obtained from the same nontrivial involution z. -/
theorem reverse_delta (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (ht : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) : centralizer (L : Set G) ∈ delta (L.conjBy g) := by
  have hs := reverse_sylow h hR e ht
  refine ⟨⟨g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [centralizer_conjugate, conjBy_inv]
  · rw [centralizer_conjugate]
    exact Ne.symm h.mem_delta.2.1
  · let a := (⟨z, hs.le (z_mem_commutingSylow h)⟩ :
      ↥(centralizer (L : Set G) ⊓ normalizer (centralizer (L.conjBy g : Set G) : Set G)))
    have ha : orderOf a = 2 :=
      (orderOf_injective _ (Subgroup.subtype_injective _) a).symm.trans h.involution
    exact even_iff_two_dvd.mpr (ha ▸ orderOf_dvd_natCard a)

/-- Failure of reverse Δ₀, using precisely the order bound 16.4.9(1),
forces |T_C|=2 and puts z outside the inner-automorphism product K′L′. -/
theorem contrary_small_outer (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (ht : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hsmall : ∀ J ∈ delta (L.conjBy g), J ∉ deltaZero (L.conjBy g) →
      ∀ S, SylowIn S (J ⊓ normalizer (centralizer (L.conjBy g : Set G) : Set G)) →
        Nat.card S = 2)
    (hnot : centralizer (L : Set G) ∉ deltaZero (L.conjBy g)) :
    Nat.card (commutingSylow T L) = 2 ∧
      z ∉ centralizer (L.conjBy g : Set G) ⊔ L.conjBy g := by
  have hd := reverse_delta h hR e ht
  have hs := reverse_sylow h hR e ht
  have hc := hsmall _ hd hnot _ hs
  refine ⟨hc, ?_⟩
  intro hz
  apply hnot
  refine ⟨hd, commutingSylow T L, hs, ?_⟩
  have heq : zpowers z = commutingSylow T L :=
    eq_of_le_of_card_ge (zpowers_le.mpr (z_mem_commutingSylow h))
      (by rw [Nat.card_zpowers, h.involution, hc])
  exact (omegaOneAmbient_le _).trans (heq ▸ zpowers_le.mpr hz)

/-- Source 16.4.2(5) gives control of C_G(r) in N_G(L′). -/
theorem involution_centralizer_control (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2) :
    centralizer ({r} : Set G) ≤ normalizer (L.conjBy g : Set G) := by
  have hn := h.normalizer_le (Q := zpowers r)
    (zpowers_ne_bot.mpr (fun he => by simp [he] at hr2)) (zpowers_le.mpr hr)
  rw [← centralizer_conjugate, normalizers_conjugate h.normalizers_eq] at hn
  apply le_trans _ hn
  apply le_trans _ (centralizer_le_normalizer (zpowers r : Set G))
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((show Commute r x from mem_centralizer_iff.mp hx r (by simp)).zpow_left n).eq

/-- Every element of the inner centralizer lies in C_H′(z). -/
theorem inner_centralizer_le (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2) :
    L ⊓ centralizer ({r} : Set G) ≤
      normalizer (L.conjBy g : Set G) ⊓ centralizer ({z} : Set G) :=
  le_inf (inf_le_right.trans (involution_centralizer_control h hr hr2))
    (inf_le_left.trans h.component.1)

omit [Finite G] in
/-- Normalizers of the fixed subgroup also normalize its characteristic residual. -/
theorem normalizes_residual (M : Subgroup G) (t : G) :
    normalizer (M : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (residual M t : Set G) := by
  have hc : normalizer (M : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (M ⊓ centralizer ({t} : Set G) : Set G) :=
    (inf_le_inf_left _ (centralizer ({t} : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  apply le_normalizer_iff.mpr
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hy
  let f := (M ⊓ centralizer ({t} : Set G)).normalizerMonoidHom ⟨x, hc hx⟩
  exact ⟨f a, map_pResidual_le 2 f.toMonoidHom ⟨a, ha, rfl⟩, rfl⟩

/-- The reversed 16.4.8 placement gives L_z ⊴ L_r, with normality
relative to L_r (indeed to C_L(r)), rather than to the ambient group. -/
theorem residual_relative_normal {M : Subgroup G} {r : G}
    (hz : z ∈ centralizer (L : Set G))
    (hr : r ∈ centralizer (M : Set G))
    (hcontrol : centralizer ({r} : Set G) ≤ normalizer (M : Set G))
    (hplace : residual M z ≤ L) :
    residual M z ≤ residual L r ∧
      ((residual M z).subgroupOf (residual L r)).Normal ∧
      L ⊓ centralizer ({r} : Set G) ≤ normalizer (residual M z : Set G) := by
  have hcent : residual M z ≤ centralizer ({r} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hr x ((residual_le M z hx).1))
  have hle : residual M z ≤ residual L r := by
    have hp : IsPPerfect 2 (residual M z) :=
      isPPerfect_embedded_pResidual 2 (M ⊓ centralizer ({z} : Set G))
    have hinc := le_inf hplace hcent
    have hm := map_pResidual_le 2 (inclusion hinc)
    rw [(pResidual_eq_top_iff 2 _).mpr hp] at hm
    intro x hx
    exact ⟨inclusion hinc ⟨x, hx⟩, hm ⟨⟨x, hx⟩, mem_top _, rfl⟩, rfl⟩
  have hn : L ⊓ centralizer ({r} : Set G) ≤ normalizer (residual M z : Set G) := by
    apply le_trans _ (normalizes_residual M z)
    refine le_inf (inf_le_right.trans hcontrol) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz x hx.1)
  exact ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr
    ((residual_le L r).trans hn), hn⟩

omit [Finite G] in
/-- The cover branch: commuting factors of an involution have the same square.
An order-four inner lift forces an order-four factor in T_C. -/
theorem cover_factor_order_four {r c l : G}
    (hcomm : Commute c l) (hr : orderOf r = 2)
    (hfactor : r = c * l) (hl : orderOf l = 4) : orderOf c = 4 := by
  have hs : c ^ 2 * l ^ 2 = 1 := by
    rw [← hcomm.mul_pow, ← hfactor, ← hr, pow_orderOf_eq_one]
  have hcs : c ^ 2 = (l ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hs
  have hc4 : c ^ 4 = 1 := by
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by rw [← pow_mul]
      _ = ((l ^ 2) ^ 2)⁻¹ := by rw [hcs, inv_pow]
      _ = 1 := by rw [← pow_mul, show 2 * 2 = 4 from rfl, ← hl, pow_orderOf_eq_one, inv_one]
  have hc2 : c ^ 2 ≠ 1 := by
    rw [hcs]
    intro hh
    have he : l ^ 2 = 1 := inv_eq_one.mp hh
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hl] at hd
    norm_num at hd
  have hd := orderOf_dvd_of_pow_eq_one hc4
  have hh := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp
    (show orderOf c ∣ 2 ^ 2 by simpa using hd)
  obtain ⟨i, hi, he⟩ := hh
  interval_cases i
  · simp only [pow_zero] at he
    exact (hc2 (by rw [orderOf_eq_one_iff.mp he]; simp)).elim
  · simp only [pow_one] at he
    exact (hc2 (he ▸ pow_orderOf_eq_one c)).elim
  · exact he

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
