module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Choice
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Selection
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Action
public import Theory.ElementaryAbelian.Basic

/-!
# Common deductions in the order-two argument

Tight embedding proves faithfulness of R on L. The earlier residual transfer
D ≤ L′ embeds R into C_H*(D*). This gives the order-two-or-four dichotomy and
completes case (I) from its intrinsic quotient centralizer bound.
The alternative formulation using the Sylow two-order also permits odd
elements of that centralizer, as required for an abelian odd residual.

For case (III), the equivalence R ≃ N_TC(K′) transfers exponent two to the
commuting factor and contradicts an order-four component lift. Independently,
TC ≤ Z(T) implies that R centralizes every containing two-subgroup of H′:
conjugate that subgroup into Tᵍ inside H′ and use R ≤ K′. The M₁₂ model
must still supply the component lift in the cover case, and both TC ≤ Z(T)
and the noncommuting Sylow-centralizer witness in the trivial-cover case.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.9(1), printed p.1189. The intrinsic centralizer cases
are separate prerequisites; these lemmas do not assert the full source theorem.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo
open OuterResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}


/-- Tight embedding gives R ∩ K = 1 directly: its order is both odd and a power of two. -/
theorem faithful (h : IntersectionSetup T z L g R) :
    Disjoint R (centralizer (L : Set G)) := by
  let U := R ⊓ centralizer (L : Set G)
  let J := (centralizer (L : Set G)).conjBy g
  have hu : IsPGroup 2 U := h.sylow.isPGroup.to_le inf_le_left
  have hle : U ≤ J ⊓ centralizer (L : Set G) :=
    inf_le_inf (h.sylow.le.trans inf_le_left) le_rfl
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hu
  have hcop : (Nat.card U).Coprime (Nat.card ↥(J ⊓ centralizer (L : Set G))) := by
    rw [hn]
    exact (odd_centralizer_intersection_of_mem_delta h.tight h.mem_delta).coprime_two_left.pow_left n
  have hb := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [inf_eq_left.mpr hle] at hb
  exact disjoint_iff.mpr hb

/-- The earlier containment D ≤ L′ implies R ≤ C_G(D), since R ≤ K′. -/
theorem centralizes_residual (h : IntersectionSetup T z L g R) {r : G}
    (hres : involutionResidual L r ≤ L.conjBy g) :
    R ≤ centralizer (involutionResidual L r : Set G) := by
  apply le_trans (h.sylow.le.trans inf_le_left)
  have he : (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) :=
    map_centralizer_equiv _ (MulAut.conj g)
  rw [he]
  exact centralizer_le hres

/-- Faithfulness and residual transfer make |R| divide |C_H*(D*)|. -/
theorem card_dvd_residualCentralizer (h : IntersectionSetup T z L g R) {r : G}
    (hres : involutionResidual L r ≤ L.conjBy g) :
    Nat.card R ∣ Nat.card (residualCentralizer L r) := by
  let hN : R ≤ normalizer (L : Set G) := h.le_sylow.trans h.sylow_normalizes
  exact card_dvd_of_injective (residualCentralizerMap hN (centralizes_residual h hres))
    (residualCentralizerMap_injective hN _ (faithful h))

/-- An order-two residual centralizer forces |R| = 2. -/
theorem card_two_of_residualCentralizer_card_two
    (h : IntersectionSetup T z L g R) {r : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hres : involutionResidual L r ≤ L.conjBy g)
    (hc : Nat.card (residualCentralizer L r) = 2) : Nat.card R = 2 := by
  have hd := card_dvd_residualCentralizer h hres
  rw [hc] at hd
  apply Nat.dvd_antisymm hd
  have ho : orderOf (⟨r, hr⟩ : R) = 2 := (orderOf_coe _).symm.trans hr2
  exact ho ▸ orderOf_dvd_natCard (⟨r, hr⟩ : R)

/-- Case (I) needs only the two-part of the residual-centralizer order.
This permits the odd elements present when the residual is abelian. -/
theorem card_two_of_residualCentralizer_sylow_two
    (h : IntersectionSetup T z L g R) {r : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hres : involutionResidual L r ≤ L.conjBy g)
    (S : Sylow 2 (residualCentralizer L r)) (hS : Nat.card S = 2) :
    Nat.card R = 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.sylow.isPGroup
  have hd := card_dvd_residualCentralizer h hres
  rw [hn] at hd
  have hdS := S.pow_dvd_card_of_pow_dvd_card hd
  rw [hS, ← hn] at hdS
  apply Nat.dvd_antisymm hdS
  have ho : orderOf (⟨r, hr⟩ : R) = 2 := (orderOf_coe _).symm.trans hr2
  exact ho ▸ orderOf_dvd_natCard (⟨r, hr⟩ : R)

/-- The source order dichotomy in the two exceptional E₄ cases. -/
theorem card_two_or_four_of_residualCentralizer_card_four
    (h : IntersectionSetup T z L g R) {r : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hres : involutionResidual L r ≤ L.conjBy g)
    (hc : Nat.card (residualCentralizer L r) = 4) :
    Nat.card R = 2 ∨ Nat.card R = 4 := by
  have hd := card_dvd_residualCentralizer h hres
  rw [hc] at hd
  have ho : orderOf (⟨r, hr⟩ : R) = 2 := (orderOf_coe _).symm.trans hr2
  have ht : 2 ∣ Nat.card R := ho ▸ orderOf_dvd_natCard (⟨r, hr⟩ : R)
  have hh := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (show Nat.card R ∣ 2 ^ 2 from hd)
  obtain ⟨k, hk, he⟩ := hh
  interval_cases k
  · rw [he] at ht
    norm_num at ht
  · exact Or.inl he
  · exact Or.inr he

/-- If the orders agree, the actual action map identifies R with C_H*(D*). -/
noncomputable def residualCentralizerEquiv
    (h : IntersectionSetup T z L g R) {r : G}
    (hres : involutionResidual L r ≤ L.conjBy g)
    (hc : Nat.card R = Nat.card (residualCentralizer L r)) :
    R ≃* residualCentralizer L r :=
  MulEquiv.ofBijective
    (residualCentralizerMap (h.le_sylow.trans h.sylow_normalizes)
      (centralizes_residual h hres))
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨residualCentralizerMap_injective _ _ (faithful h), hc⟩)

/-- Lift case (I) from H* to C_H(D) ≤ K⟨r⟩ using the canonical quotient kernel. -/
theorem centralizer_bound_of_quotient_bound
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hc : residualCentralizer L r ≤
      zpowers (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))) :
    normalizer (centralizer (L : Set G) : Set G) ⊓
        centralizer (involutionResidual L r : Set G) ≤
      centralizer (L : Set G) ⊔ zpowers r := by
  intro x hx
  let A := normalizer (centralizer (L : Set G) : Set G) ⊓
    centralizer (involutionResidual L r : Set G)
  have hA : A ≤ normalizer (L : Set G) :=
    inf_le_left.trans h.normalizers_eq.le
  have hxC := actionMap_mem_residualCentralizer hA inf_le_right (⟨x, hx⟩ : A)
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hc hxC)
  let a : normalizer (L : Set G) := ⟨x, hA hx⟩
  let b : normalizer (L : Set G) := ⟨r, h.sylow_normalizes (h.le_sylow hr)⟩
  have he : quotientMap L a = quotientMap L (b ^ n) := by
    rw [map_zpow]
    exact hn.symm
  have hxK' : a / b ^ n ∈
      (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) :=
    QuotientGroup.eq_iff_div_mem.mp he
  have hxK : x / r ^ n ∈ centralizer (L : Set G) :=
    hxK'
  have hp : x / r ^ n * r ^ n ∈ centralizer (L : Set G) ⊔ zpowers r :=
    (centralizer (L : Set G) ⊔ zpowers r).mul_mem
      ((le_sup_left : centralizer (L : Set G) ≤ centralizer (L : Set G) ⊔ zpowers r) hxK)
      ((le_sup_right : zpowers r ≤ centralizer (L : Set G) ⊔ zpowers r)
        (zpow_mem_zpowers r n))
  simpa only [div_mul_cancel] using hp

/-- Complete the ambient algebra of case (I) from its intrinsic quotient bound. -/
theorem card_two_of_quotient_bound
    (h : IntersectionSetup T z L g R) {r : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hres : involutionResidual L r ≤ L.conjBy g)
    (hc : residualCentralizer L r ≤
      zpowers (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))) :
    Nat.card R = 2 := by
  exact sylow_card_two_of_centralizer_bound h.sylow (faithful h)
    (centralizes_residual h hres) hr hr2
    (centralizer_bound_of_quotient_bound h hr hc)

/-- The equivalence R ≃ N_TC(K′) from 16.4.2(1) transfers exponent two to the commuting factor. -/
theorem normalizer_factor_pow_two
    (h : IntersectionSetup T z L g R) {r : G}
    (hres : involutionResidual L r ≤ L.conjBy g)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    {c : G} (hc : c ∈ commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)) : c ^ 2 = 1 := by
  let f := residualCentralizerMap (h.le_sylow.trans h.sylow_normalizes)
    (centralizes_residual h hres)
  have hf : Function.Injective f := residualCentralizerMap_injective _ _ (faithful h)
  have he : f (e.symm ⟨c, hc⟩) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) _
  have hpow : (e.symm ⟨c, hc⟩) ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using he)
  have hc2 := congrArg e hpow
  have hc2' : (⟨c, hc⟩ : ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G))) ^ 2 = 1 := by
    simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using hc2
  exact congrArg Subtype.val hc2'

/-- The cover contradiction in case (III), once I.2.2(5b) supplies the actual order-four component lift. -/
theorem no_order_four_component_lift
    (h : IntersectionSetup T z L g R) {r : G}
    (hres : involutionResidual L r ≤ L.conjBy g)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    {s c v : G} (hs : orderOf s = 2)
    (hc : c ∈ commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hv : v ∈ L) (hsv : s = v * c) (hv4 : orderOf v = 4) : False := by
  have hc2 : c ^ 2 = 1 := normalizer_factor_pow_two h hres e hc
  have hcomm : Commute v c := mem_centralizer_iff.mp hc.1.2 v hv
  have hs2 : s ^ 2 = 1 := (orderOf_eq_prime_iff.mp hs).1
  have hv2 : v ^ 2 = 1 := by
    simpa only [hsv, hcomm.mul_pow, hc2, mul_one] using hs2
  have hd := orderOf_dvd_of_pow_eq_one hv2
  rw [hv4] at hd
  omega

/-- The final Sylow-conjugacy step in case (III): if TC is central in T, R centralizes every containing two-subgroup of H′. -/
theorem centralizes_of_commutingSylow_central
    (h : IntersectionSetup T z L g R)
    (hcentral : commutingSylow T L ≤ centralizer (T : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hRP : R ≤ P) : R ≤ centralizer (P : Set G) := by
  have hTN : (T : Subgroup G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    h.normalizers_eq ▸ h.sylow_normalizes
  have hTS : SylowIn (T : Subgroup G)
      (normalizer (centralizer (L : Set G) : Set G)) :=
    ⟨T.subtype hTN, map_subgroupOf_eq_of_le hTN⟩
  have hTg : SylowIn ((T : Subgroup G).conjBy g)
      (normalizer ((centralizer (L : Set G)).conjBy g : Set G)) := by
    have hm := hTS.map (MulAut.conj g)
    rwa [map_equiv_normalizer_eq] at hm
  obtain ⟨a, ha, hPa⟩ := hTg.exists_conjugate_le hP hPH
  have hRaK : R.conjBy a ≤ (centralizer (L : Set G)).conjBy g := by
    have hm := map_mono (f := (MulAut.conj a).toMonoidHom)
      (h.sylow.le.trans inf_le_left)
    change R.conjBy a ≤ ((centralizer (L : Set G)).conjBy g).conjBy a at hm
    have haeq : ((centralizer (L : Set G)).conjBy g).conjBy a =
        (centralizer (L : Set G)).conjBy g := mem_normalizer_iff_map_conj_eq.mp ha
    rwa [haeq] at hm
  have hRaT : R.conjBy a ≤ (T : Subgroup G).conjBy g := (map_mono hRP).trans hPa
  have hRaC : R.conjBy a ≤ (commutingSylow T L).conjBy g := by
    change R.conjBy a ≤ ((T : Subgroup G) ⊓ centralizer (L : Set G)).map
      (MulAut.conj g).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    exact le_inf hRaT hRaK
  have hCg : (commutingSylow T L).conjBy g ≤
      centralizer ((T : Subgroup G).conjBy g : Set G) := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hcentral
    rwa [map_centralizer_equiv] at hm
  have hc : R.conjBy a ≤ centralizer (P.conjBy a : Set G) :=
    hRaC.trans (hCg.trans (centralizer_le hPa))
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  apply (MulAut.conj a).injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
    mem_centralizer_iff.mp (hc ⟨x, hx, rfl⟩) _ ⟨y, hy, rfl⟩

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo
