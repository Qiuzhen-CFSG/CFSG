module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.QuotientOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Setup

/-!
# The original module survives central projection with its covering quotient

For a covering subgroup B of L, a central two-group kernel kills only vectors
in C_V(L). Its image therefore retains a quotient isomorphic to the original
V/C_V(L) inside its two-core. Projection also retains the entire B/O₂(B),
including the cubic center of SL₃. Multiplying these two orders proves that
2¹² divides the central quotient of every ordinary pushing-up component.

SmallSylow excludes M₂₄, J₂ and He using this bound; FinalOrdinary applies
the stronger product formula to the remaining rows. All projections use the
original inclusions and chosen central quotient, without splitting V.
Source: Aschbacher--Smith C.3.2--5, pp.149--150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- Central projection retains the module quotient and the full actor quotient. -/
theorem natural_cover_projection_order {B : Subgroup G} (hBL : B ≤ L)
    (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    {Q : Type*} [Group Q] [Finite Q] (f : B →* Q)
    (hk : IsPGroup 2 f.ker) (hz : f.ker ≤ center B) :
    Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card f.range := by
  have hVB' : V ≤ B := hVB.trans (pCoreIn_le 2 B)
  let g := f.rangeRestrict.comp (inclusion hVB')
  have hgker : g.ker ≤ D.toCentralQuotient.ker := by
    intro v hv
    apply (quotient_eq_one_iff D v).mpr
    have hb : (v : G) ∈ centralizer (B : Set G) := by
      intro b hb
      exact congrArg Subtype.val ((mem_center_iff.mp (hz
        (show inclusion hVB' v ∈ f.ker from congrArg Subtype.val hv))) ⟨b,hb⟩)
    have hq : (v : G) ∈ centralizer (L.pCoreIn 2 : Set G) := by
      exact le_centralizer_iff.mp
        ((centralizer_eq_core D S).ge.trans inf_le_right) v.property
    intro l hl
    obtain ⟨b,hb',q,hq',rfl⟩ := hc ▸ hl
    calc
      b * q * (v : G) = b * ((v : G) * q) := by rw [mul_assoc, hq q hq']
      _ = (v : G) * (b * q) := by rw [←mul_assoc, hb b hb', mul_assoc]
  let j := QuotientGroup.lift g.ker D.toCentralQuotient hgker
  have hj : Function.Surjective j := QuotientGroup.lift_surjective_of_surjective
    g.ker D.toCentralQuotient D.toCentralQuotient_surjective hgker
  have hd : Nat.card D.chosenCentralQuotient ∣ Nat.card g.range := by
    have hd := card_dvd_of_surjective j hj
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  have hgcore : g.range ≤ pCore 2 f.range := by
    rintro _ ⟨v,rfl⟩
    have hpre := f.rangeRestrict.comap_pCore_of_ker_isPGroup (p := 2)
      f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
    change inclusion hVB' v ∈ (pCore 2 f.range).comap f.rangeRestrict
    rw [hpre]
    obtain ⟨b,hb,he⟩ := hVB v.property
    exact (Subtype.ext he : b = inclusion hVB' v) ▸ hb
  have hdc : Nat.card D.chosenCentralQuotient ∣ Nat.card (pCore 2 f.range) :=
    hd.trans (card_dvd_of_le hgcore)
  obtain ⟨e,_⟩ := cover_quotient hBL hc.subset
  let eq := e.symm.trans (f.rangeRestrict.quotientPCoreEquivOfSurjective
    f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hk))
  rw [Nat.card_congr eq.toEquiv, card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range), mul_comm]
  exact Nat.mul_dvd_mul (dvd_refl _) hdc

/-- Both original natural objects have order divisible by 64. -/
theorem natural_two_parts :
    64 ∣ Nat.card D.chosenCentralQuotient ∧ 64 ∣ Nat.card (L ⧸ pCore 2 L) := by
  have hp (d : ℕ) (hd : 3 ≤ d) : 64 ∣ Nat.card S.field.Carrier ^ d := by
    rw [S.field.card_eq, ← pow_mul]
    change 2 ^ 6 ∣ 2 ^ (S.field.degree * d)
    apply pow_dvd_pow 2
    have := S.nonbinary
    nlinarith
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_fin,
      Nat.card_congr hm.some.groupEquiv.toEquiv, linear_three_order]
    exact ⟨hp 3 le_rfl, (hp 3 le_rfl).mul_right _ |>.mul_right _⟩
  | sp4 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_sum,
      Nat.card_fin,
      Nat.card_congr hm.some.groupEquiv.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp]
    exact ⟨hp 4 (by decide), (hp 4 (by decide)).mul_right _ |>.mul_right _⟩
  | g2 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := S.field.Carrier), Atlas.G2.Natural.finrank_space,
      Nat.card_congr hm.some.groupEquiv.toEquiv, Atlas.G2.card_Model]
    exact ⟨hp 6 (by decide), (hp 6 (by decide)).mul_right _ |>.mul_right _⟩

/-- The literal ordinary-component projection satisfies the product-order bound. -/
theorem ordinary_natural_product_card_dvd {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣
      Nat.card (K ⧸ center K) := by
  let BH := B.subgroupOf H
  let BK := BH.subgroupOf K
  have hBH : B ≤ H := h.component_le.trans h.local_le
  have hBK : BH ≤ K := h.ordinary_component_contains_original K hK
  let eb : BK ≃* B := (subgroupOfEquivOfLe hBK).trans (subgroupOfEquivOfLe hBH)
  let j : B →* K := BK.subtype.comp eb.symm.toMonoidHom
  have hj : Function.Injective j := BK.subtype_injective.comp eb.symm.injective
  let f := (QuotientGroup.mk' (center K)).comp j
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (center K)).comp j).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup.comap_of_injective j hj
  have hcentral : f.ker ≤ center B := by
    intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using
      (mem_center_iff.mp ((QuotientGroup.eq_one_iff (j b)).mp hb)) (j c)
  have hd := natural_cover_projection_order D S hBL hc hVB f hk hcentral
  exact hd.trans f.range.card_subgroup_dvd_card

/-- The natural module and full quotient together retain at least twelve binary factors. -/
theorem ordinary_natural_two_power_dvd {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (K : Subgroup H) (hK : IsComponent H K) :
    2 ^ 12 ∣ Nat.card (K ⧸ center K) := by
  obtain ⟨hv,hq⟩ := natural_two_parts D S
  have hd : 2 ^ 12 ∣ Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) := by
    simpa only [show (64 * 64 : ℕ) = 2 ^ 12 by decide] using Nat.mul_dvd_mul hv hq
  exact hd.trans (ordinary_natural_product_card_dvd D S h hBL hc hVB K hK)

/-- Relative normality of the covering residual places the same V in its two-core. -/
theorem covering_module_le_core {M B : Subgroup G}
    (hBL : B ≤ L) (hBM : B ≤ M) (hVM : V ≤ M) (hN : (B.subgroupOf M).Normal)
    (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G)) : V ≤ B.pCoreIn 2 := by
  have hQ : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (centralizer_eq_core D S).ge.trans inf_le_right
  have he := D.eq_commutator.trans
    (commutator_eq_of_product_centralizing_factor hc (le_centralizer_iff.mp hQ))
  have hn : V ≤ normalizer (B : Set G) :=
    hVM.trans ((normal_subgroupOf_iff_le_normalizer hBM).mp hN)
  have hv : V ≤ B := he ▸ le_normalizer_iff_commutator_le_right.mp hn
  let := D.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hv
    (hBL.trans D.normalizes)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
