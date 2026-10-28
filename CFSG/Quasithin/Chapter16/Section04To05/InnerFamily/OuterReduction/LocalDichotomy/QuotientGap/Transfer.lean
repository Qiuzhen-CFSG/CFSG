module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientSetup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.ProductIdentification
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import Theory.GroupAction.CentralQuotientFusionGap

/-!
# Quotient transfer in the empty-family argument

The action of r on L/O₂(L) has order two and is outer. We identify this
quotient with the actual subgroup L* of H/K, where H = N_G(L) and
K = C_G(L), using the proved equality Z(L) = O₂(L).

The geometric equality r^L ∩ C_G(r) = {r, rz} bounds fixed displacements.
When r fixes the covering center pointwise, central-quotient displacement
then proves the index-two and fusion assertions, and a quotient displacement
of order two supplies the missing involution. The center-fixation premise
is retained explicitly: none of these conditional results discharges it.
In particular we do not assume that the covering center has order two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1190, after the commuting-conjugate equality.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap
open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] {L : Subgroup G} {r z : G}

/-- Identify L/O₂(L) with L*, retaining its embedding in the fixed H/K. -/
noncomputable def coreQuotientEquivStar (hc : center L = pCore 2 L) :
    (L ⧸ pCore 2 L) ≃* OrderTwo.actionImage L L :=
  (QuotientGroup.quotientMulEquivOfEq hc.symm).trans
    (OrderTwo.centerQuotientEquivActionImage L)

/-- The canonical embedding of the component quotient into H/K. -/
noncomputable def coreQuotientToStar (hc : center L = pCore 2 L) :
    (L ⧸ pCore 2 L) →* OrderTwo.ActionQuotient L :=
  (OrderTwo.actionImage L L).subtype.comp (coreQuotientEquivStar hc).toMonoidHom

theorem coreQuotientToStar_mk (hc : center L = pCore 2 L) (x : L) :
    coreQuotientToStar hc (QuotientGroup.mk' (pCore 2 L) x) =
      OrderTwo.actionMap L.le_normalizer x := rfl

theorem coreQuotientToStar_injective (hc : center L = pCore 2 L) :
    Function.Injective (coreQuotientToStar hc) :=
  Subtype.val_injective.comp (coreQuotientEquivStar hc).injective

theorem coreQuotientToStar_range (hc : center L = pCore 2 L) :
    (coreQuotientToStar hc).range = OrderTwo.actionImage L L := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact (coreQuotientEquivStar hc q).property
  · intro hx
    exact ⟨(coreQuotientEquivStar hc).symm ⟨x, hx⟩,
      congrArg Subtype.val ((coreQuotientEquivStar hc).apply_symm_apply ⟨x, hx⟩)⟩

/-- The quotient action is precisely conjugation by the actual r* in H/K. -/
theorem coreQuotientToStar_action (hc : center L = pCore 2 L)
    (hn : r ∈ normalizer (L : Set G)) (q : L ⧸ pCore 2 L) :
    coreQuotientToStar hc (quotientAction hn q) =
      MulAut.conj (OrderTwo.actionElement L r hn) (coreQuotientToStar hc q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [quotientAction_apply, coreQuotientToStar_mk, coreQuotientToStar_mk]
  change OrderTwo.quotientMap L
    (⟨r, hn⟩ * ⟨x, L.le_normalizer x.property⟩ * ⟨r, hn⟩⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- Under the canonical embedding, the centralizer image is exactly C_L(r)*. -/
theorem centralizerImage_map_toStar (hc : center L = pCore 2 L)
    (hn : r ∈ normalizer (L : Set G)) :
    (centralizerImage hn).map (coreQuotientToStar hc) =
      OrderTwo.actionImage L (L ⊓ involutionCentralizer r) := by
  ext s
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    rw [coreQuotientToStar_mk]
    exact OrderTwo.mem_actionImage _ ⟨x.property, (mem_fixed_action hn x).mp hx⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨QuotientGroup.mk' (pCore 2 L) ⟨x, hx.1⟩,
      ⟨⟨x, hx.1⟩, (mem_fixed_action hn _).mpr hx.2, rfl⟩, ?_⟩
    rw [coreQuotientToStar_mk]
    rfl

/-- Multiplying a conjugate of r* by r* is the embedded quotient displacement. -/
theorem star_conjugate_product (hc : center L = pCore 2 L)
    (hn : r ∈ normalizer (L : Set G)) (hr2 : orderOf r = 2)
    (q : L ⧸ pCore 2 L) :
    OrderTwo.actionElement L r hn *
        MulAut.conj (coreQuotientToStar hc q) (OrderTwo.actionElement L r hn) =
      coreQuotientToStar hc (quotientAction hn q * q⁻¹) := by
  have hrr : OrderTwo.actionElement L r hn * OrderTwo.actionElement L r hn = 1 := by
    change OrderTwo.quotientMap L ⟨r, hn⟩ * OrderTwo.quotientMap L ⟨r, hn⟩ = 1
    rw [← map_mul, show (⟨r, hn⟩ : normalizer (L : Set G)) * ⟨r, hn⟩ = 1 from
      Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two, hr2]
        using pow_orderOf_eq_one r), map_one]
  have hi := inv_eq_of_mul_eq_one_right hrr
  rw [map_mul, map_inv, coreQuotientToStar_action, MulAut.conj_apply, MulAut.conj_apply, hi]
  group

/-- The geometric conjugacy bound, expressed as a bound on fixed displacements. -/
theorem fixed_displacement_cases (hn : r ∈ normalizer (L : Set G))
    (hr2 : orderOf r = 2) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (x : L) (hx : action hn (action hn x * x⁻¹) = action hn x * x⁻¹) :
    action hn x * x⁻¹ = 1 ∨ action hn x * x⁻¹ = (⟨z, hzL⟩ : L) := by
  have hrr : r * r = 1 := by simpa only [pow_two, hr2] using pow_orderOf_eq_one r
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hd : ((action hn x * x⁻¹ : L) : G) = r * MulAut.conj (x : G) r := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, action_apply, MulAut.conj_apply, hri]
    group
  have hdf : ((action hn x * x⁻¹ : L) : G) ∈ involutionCentralizer r :=
    (mem_fixed_action hn _).mp ((MulAut.mem_fixedSubgroup _ _).mpr hx)
  have hcomm : Commute r (MulAut.conj (x : G) r) := by
    have hh := mem_centralizer_singleton_iff.mp hdf
    rw [hd] at hh
    have hh' : r * (MulAut.conj (x : G) r * r) = r * (r * MulAut.conj (x : G) r) := by
      simpa only [mul_assoc] using hh
    exact (mul_left_cancel hh').symm
  have hcases : MulAut.conj (x : G) r = r ∨ MulAut.conj (x : G) r = r * z := by
    have hm : MulAut.conj (x : G) r ∈
        {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} :=
      ⟨⟨x, x.property, rfl⟩, hcomm⟩
    rw [hgeom] at hm
    exact hm
  rcases hcases with he | he
  · left
    apply Subtype.ext
    simpa only [he, hrr, Subgroup.coe_one] using hd
  · right
    apply Subtype.ext
    simpa only [he, ← mul_assoc, hrr, one_mul] using hd

variable [Finite G] {𝒦 : GroupClass} {T : Sylow 2 G} {g : G} {R : Subgroup G}

/-- Outer conjugation remains outer on the actual quotient by O₂(L). -/
theorem quotientAction_outer (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hn : r ∈ normalizer (L : Set G))
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    ¬ ∃ q : L ⧸ pCore 2 L, quotientAction hn = MulAut.conj q := by
  let := h.component.quasisimple
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  have hinj : Function.Injective (quotientAut (pCore 2 L)) := by
    intro a b hab
    apply MulAut.quotient_center_injective
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) q
    simp only [quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    rw [hc]
    have he := DFunLike.congr_fun hab (QuotientGroup.mk' (pCore 2 L) x)
    rw [quotientAut_apply_mk, quotientAut_apply_mk] at he
    exact QuotientGroup.eq.mp he
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  apply OrderTwo.CentralizerCases.action_not_inner L hn hout
  refine ⟨x, hinj ?_⟩
  change quotientAction hn = _
  rw [hq]
  ext y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
  simp only [quotientAut_apply_mk, MulAut.conj_apply, map_mul, map_inv]

/-- The induced automorphism has order exactly two, without any center-size assumption. -/
theorem quotientAction_order_two (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    orderOf (quotientAction hn) = 2 := by
  have ha : action hn ^ 2 = 1 := by
    change L.normalizerMonoidHom (⟨r, hn⟩ : normalizer (L : Set G)) ^ 2 = 1
    rw [← map_pow, show (⟨r, hn⟩ : normalizer (L : Set G)) ^ 2 = 1 from
      Subtype.ext (hr2 ▸ pow_orderOf_eq_one r), map_one]
  apply orderOf_eq_prime
  · change quotientAut (pCore 2 L) (action hn) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  · intro he
    exact quotientAction_outer hG h hn hout ⟨1, by simpa using he⟩

private theorem marked_z_mem_core (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hzL : z ∈ L) :
    (⟨z, hzL⟩ : L) ∈ pCore 2 L := by
  rw [← hG.evenType.component_center_eq_twoCore h.involution h.component]
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (h.component.1 x.property))

/-- Conditional index calculation. Pointwise fixation of the covering center
is a separate obligation; the geometric equality supplies the nontrivial displacement. -/
theorem imageInFixed_index_two_of_center_fixed
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfix : center L ≤ (action hn).fixedSubgroup) :
    (imageInFixed hn).index = 2 := by
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  have hfix' : pCore 2 L ≤ (action hn).fixedSubgroup := hc ▸ hfix
  have hz := marked_z_mem_core hG h hzL
  apply MulAut.CentralQuotientFusionGap.fixedImage_index_two (pCore 2 L) (action hn)
    hc.symm.le hfix' hz ((orderOf_coe _).symm.trans h.involution)
  · intro x hx
    exact fixed_displacement_cases hn hr2 hzL hgeom x
      ((MulAut.mem_fixedSubgroup _ _).mp (hfix' hx))
  · have hm : r * z ∈ {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} := by
      rw [hgeom]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    obtain ⟨⟨l, hl, he⟩, _⟩ := hm
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    have hrr : r * r = 1 := by simpa only [pow_two, hr2] using pow_orderOf_eq_one r
    have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    change r * l * r⁻¹ * l⁻¹ = z
    calc
      r * l * r⁻¹ * l⁻¹ = r * MulAut.conj l r := by rw [hri, MulAut.conj_apply]; group
      _ = z := by rw [he, ← mul_assoc, hrr, one_mul]

/-- The intrinsic form of the quotient fusion restriction. -/
theorem quotient_displacement_eq_one_of_center_fixed
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfix : center L ≤ (action hn).fixedSubgroup)
    (q : L ⧸ pCore 2 L) (hq : quotientAction hn q * q⁻¹ ∈ centralizerImage hn) :
    quotientAction hn q * q⁻¹ = 1 := by
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  exact MulAut.CentralQuotientFusionGap.quotient_displacement_eq_one
    (pCore 2 L) (action hn) (hc ▸ hfix) (marked_z_mem_core hG h hzL)
    (fixed_displacement_cases hn hr2 hzL hgeom) q hq

/-- The source fusion restriction in the fixed H/K, with both stars realized
by the canonical homomorphism rather than by a split extension. -/
theorem star_fusion_eq_singleton_of_center_fixed
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfix : center L ≤ (action hn).fixedSubgroup) :
    {s : OrderTwo.ActionQuotient L |
      (∃ v ∈ OrderTwo.actionImage L (L ⊓ involutionCentralizer r),
        s = OrderTwo.actionElement L r hn * v) ∧
      (∃ l ∈ OrderTwo.actionImage L L,
        MulAut.conj l (OrderTwo.actionElement L r hn) = s)} =
      {OrderTwo.actionElement L r hn} := by
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  have hrr : OrderTwo.actionElement L r hn * OrderTwo.actionElement L r hn = 1 := by
    change OrderTwo.quotientMap L ⟨r, hn⟩ * OrderTwo.quotientMap L ⟨r, hn⟩ = 1
    rw [← map_mul, show (⟨r, hn⟩ : normalizer (L : Set G)) * ⟨r, hn⟩ = 1 from
      Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two, hr2]
        using pow_orderOf_eq_one r), map_one]
  ext s
  constructor
  · rintro ⟨⟨v, hv, hs⟩, ⟨l, hl, he⟩⟩
    rw [← centralizerImage_map_toStar hc hn] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [← coreQuotientToStar_range hc] at hl
    obtain ⟨q, rfl⟩ := hl
    have hd : quotientAction hn q * q⁻¹ = w := by
      apply coreQuotientToStar_injective hc
      rw [← star_conjugate_product hc hn hr2, he, hs, ← mul_assoc, hrr, one_mul]
    have hw1 : w = 1 := hd.symm.trans
      (quotient_displacement_eq_one_of_center_fixed hG h hr2 hn hzL hgeom hfix q
        (hd.symm ▸ hw))
    simpa only [hw1, map_one, mul_one, Set.mem_singleton_iff] using hs
  · intro hs
    have hs' : s = OrderTwo.actionElement L r hn := hs
    subst s
    exact ⟨⟨1, one_mem _, (mul_one _).symm⟩, ⟨1, one_mem _, by simp⟩⟩

/-- The supplied quotient commuting-conjugate witness produces a missing involution. -/
theorem exists_involution_outside_image_of_center_fixed
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfix : center L ≤ (action hn).fixedSubgroup)
    (q : L ⧸ pCore 2 L) (hq2 : orderOf (quotientAction hn q * q⁻¹) = 2)
    (hqfix : quotientAction hn (quotientAction hn q * q⁻¹) = quotientAction hn q * q⁻¹) :
    ∃ v : quotientFixed hn, orderOf v = 2 ∧ v ∉ imageInFixed hn := by
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  exact MulAut.CentralQuotientFusionGap.exists_involution_outside_fixedImage
    (pCore 2 L) (action hn) (hc ▸ hfix) (marked_z_mem_core hG h hzL)
    (fixed_displacement_cases hn hr2 hzL hgeom) q hq2 hqfix

/-- The elementary-center covers with involutory lifting can be excluded
directly. These are the precise lifting clauses of I.2.2(3b),(4) needed for
the exceptional E₄ centers in 16.1.2(2); no center action is assumed. -/
theorem false_of_elementary_center_and_involution_lifting
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hcenter2 : ∀ c ∈ center L, c ^ 2 = 1)
    (hlift : ∀ v : L ⧸ pCore 2 L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (pCore 2 L) y = v ∧ y ^ 2 = 1)
    (q : L ⧸ pCore 2 L) (hq2 : orderOf (quotientAction hn q * q⁻¹) = 2) : False := by
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  have ha : action hn ^ 2 = 1 := by
    change L.normalizerMonoidHom (⟨r, hn⟩ : normalizer (L : Set G)) ^ 2 = 1
    rw [← map_pow, show (⟨r, hn⟩ : normalizer (L : Set G)) ^ 2 = 1 from
      Subtype.ext (hr2 ▸ pow_orderOf_eq_one r), map_one]
  exact MulAut.CentralQuotientFusionGap.false_of_involution_lifting
    (pCore 2 L) (action hn) hc.symm.le (hc ▸ hcenter2) ha
    (marked_z_mem_core hG h hzL) (fixed_displacement_cases hn hr2 hzL hgeom) hlift q hq2

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap
