module

public import Theory.GroupTheory.ElementarySixteenExtensionTransfer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Fixed spaces and elementary-sixteen group extensions

Let A be an elementary normal subgroup of order sixteen and L a normal
supplement with |A ∩ L| = 8. The fixed-space containment of B.4.8(3),
for the literal L/(A ∩ L) action, extends to the ambient quotient by A.
An involution power in the image of a two-subgroup proves C_T(a) ≤ A
for a ∈ A − L. If quotient involutions have involution lifts in L,
comparison with such a lift proves every outside involution lies in A.

The relative index is two. When |T ∩ L| = 64, the image T/A has order
eight, and its canonical conjugation action is regular on A − L.
The orbit theorem retains the quotient map and proves unique existence
of the acting quotient element, rather than just a cardinality equality.

Source: Aschbacher–Smith, Lemma 14.4.5, printed p.1008, using precisely
the fixed-space containment in B.4.8(3), printed p.91. The involution
lifts are a separate nonsplit-block obligation; no square or fusion
conclusion is inferred from a module name.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Extend the involution fixed-space containment from a supplement to
the whole group; the abelian kernel acts trivially. -/
public theorem fixed_bound_extend_from_normal_supplement (L A : Subgroup G) [A.Normal]
    [IsMulCommutative A] (hcover : L ⊔ A = ⊤)
    (hfixed : ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L)
    (x : G) (hx : orderOf (QuotientGroup.mk' A x) = 2)
    (a : G) (ha : a ∈ A) (hxa : Commute x a) : a ∈ L := by
  obtain ⟨y, hy, b, hb, rfl⟩ := mem_sup_of_normal_right.mp
    (show x ∈ L ⊔ A from hcover ▸ mem_top x)
  have hba : Commute b a := congrArg Subtype.val
    (mul_comm (⟨b, hb⟩ : A) (⟨a, ha⟩ : A))
  have hya : Commute y a := by
    apply mul_right_cancel (b := b)
    calc
      y * a * b = y * (b * a) := by rw [hba.eq]; group
      _ = (y * b) * a := by group
      _ = a * (y * b) := hxa.eq
      _ = a * y * b := by group
  apply hfixed y hy ?_ a ha hya
  have hbq : QuotientGroup.mk' A b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
  simpa only [map_mul, hbq, mul_one] using hx

/-- Fixed-space containment for quotient involutions bounds centralizers
in every two-subgroup, including elements of order greater than two. -/
public theorem centralizer_bound_of_quotient_involution_fixed
    (T L A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hT : IsPGroup 2 T) (hcover : L ⊔ A = ⊤)
    (hfixed : ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L)
    (a : G) (ha : a ∈ A) (haL : a ∉ L) :
    T ⊓ centralizer ({a} : Set G) ≤ A := by
  intro x hx
  by_contra hxA
  let π := QuotientGroup.mk' A
  let q : T.map π := ⟨π x, mem_map_of_mem π hx.1⟩
  have hq : q ≠ 1 := by
    intro h
    exact hxA ((QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val h))
  have hdiv : 2 ∣ orderOf (π x) := by
    simpa only [← Subgroup.orderOf_coe] using (hT.map π).dvd_orderOf hq
  let n := orderOf (π x) / 2
  have hn : orderOf (π (x ^ n)) = 2 := by
    rw [map_pow]
    exact orderOf_pow_orderOf_div (orderOf_pos (π x)).ne' hdiv
  have hc : Commute x a := mem_centralizer_singleton_iff.mp hx.2
  exact haL (fixed_bound_extend_from_normal_supplement L A hcover hfixed (x^n) hn a ha (hc.pow_left n))

omit [Finite G] in
/-- Comparing involution lifts rules out square-one elements outside
both the supplement and the elementary kernel. -/
public theorem outside_involution_mem_of_involution_lifts
    (L A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hfixed : ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L)
    (hlift : ∀ q : G ⧸ A, orderOf q = 2 →
      ∃ y ∈ L, y^2 = 1 ∧ QuotientGroup.mk' A y = q)
    (x : G) (hxL : x ∉ L) (hx2 : x^2 = 1) : x ∈ A := by
  by_contra hxA
  let π := QuotientGroup.mk' A
  have hq : orderOf (π x) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hx2, map_one])
    (fun h => hxA ((QuotientGroup.eq_one_iff x).mp h))
  obtain ⟨y, hy, hy2, hyq⟩ := hlift (π x) hq
  let a := y⁻¹ * x
  have ha : a ∈ A := (QuotientGroup.eq_one_iff a).mp (by
    change π (y⁻¹*x) = 1
    rw [map_mul, map_inv, hyq, inv_mul_cancel])
  have ha2 : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hxa : x = y*a := by dsimp [a]; group
  have hya : Commute y a := by
    have hix : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
    have hiy : y⁻¹=y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy2)
    have hia : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
    change y*a=a*y
    calc
      y*a = x⁻¹ := hxa.symm.trans hix.symm
      _ = a*y := by rw [hxa, mul_inv_rev, hiy, hia]
  have haL := hfixed y hy (hyq ▸ hq) a ha hya
  exact hxL (hxa ▸ L.mul_mem hy haL)


omit [Finite G] in
/-- The index-two conclusion is relative to the supplied subgroup T. -/
public theorem relative_index_two_of_elementary_extension
    (T L A : Subgroup G) [L.Normal]
    (hAT : A ≤ T) (hcover : L ⊔ A = ⊤)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8) :
    (L.subgroupOf T).index = 2 := by
  have hcard : Nat.card (L.subgroupOf A) = 8 := by
    rw [← inf_subgroupOf_right L A]
    exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans hV
  have hi := (L.subgroupOf A).index_mul_card
  rw [hcard, hA] at hi
  have hLA : L.relIndex A = 2 := by change (L.subgroupOf A).index = 2; omega
  have hLT : L ⊔ T = ⊤ := top_unique (hcover ▸ sup_le_sup_left hAT L)
  change L.relIndex T = 2
  rw [← relIndex_sup_left T L, hLT, ← hcover, relIndex_sup_left, hLA]

omit [Finite G] in
/-- The order-64 intersection gives the actual quotient image order eight. -/
public theorem sylow_image_card_of_elementary_extension
    (T L A : Subgroup G) [L.Normal] [A.Normal]
    (hAT : A ≤ T) (hcover : L ⊔ A = ⊤)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (hTL : Nat.card (T ⊓ L : Subgroup G) = 64) :
    Nat.card (T.map (QuotientGroup.mk' A)) = 8 := by
  have hi := relative_index_two_of_elementary_extension T L A hAT hcover hA hV
  have hc : Nat.card (L.subgroupOf T) = 64 := by
    rw [← inf_subgroupOf_right L T]
    exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans
      (by simpa only [inf_comm] using hTL)
  have hT := (L.subgroupOf T).index_mul_card
  rw [hi, hc] at hT
  have hp := relIndex_mul_relIndex (⊥ : Subgroup G) A T bot_le hAT
  rw [relIndex_bot_left, relIndex_bot_left, hA, ← QuotientGroup.ker_mk' A,
    relIndex_ker] at hp
  omega


omit [Finite G] in
/-- Conjugation on an abelian normal subgroup, descended through its
actual quotient in the ambient group. -/
public noncomputable def abelianQuotientConj (A : Subgroup G) [A.Normal] [IsMulCommutative A] :
    G ⧸ A →* MulAut A :=
  QuotientGroup.lift A MulAut.conjNormal (by
    intro x hx
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change x * (a : G) * x⁻¹ = (a : G)
    have hc : x * (a : G) = a * x := congrArg Subtype.val
      (mul_comm (⟨x,hx⟩ : A) a)
    rw [hc, mul_inv_cancel_right])

omit [Finite G] in
/-- The descended action is literal ambient conjugation. -/
public theorem abelianQuotientConj_mk (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (x : G) (a : A) :
    (abelianQuotientConj A (QuotientGroup.mk' A x) a : G) = x * a * x⁻¹ := by rfl

/-- Regularity of T/A on A − L: for each ordered pair there is exactly
one element of the literal quotient image carrying the first to the second. -/
public theorem regular_quotient_action_of_fixed_bound
    (T L A : Subgroup G) [L.Normal] [A.Normal] [IsMulCommutative A]
    (hT : IsPGroup 2 T) (hcover : L ⊔ A = ⊤)
    (hfixed : ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (himage : Nat.card (T.map (QuotientGroup.mk' A)) = 8)
    (a b : A) (ha : (a : G) ∉ L) (hb : (b : G) ∉ L) :
    ∃! q : T.map (QuotientGroup.mk' A), abelianQuotientConj A q a = b := by
  classical
  let π := QuotientGroup.mk' A
  let ρ := abelianQuotientConj A
  let D := {a : A // (a : G) ∉ L}
  have hstay (q : G ⧸ A) : ((ρ q a : A) : G) ∉ L := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A q
    intro h
    have hh := (inferInstance : L.Normal).conj_mem _ h x⁻¹
    exact ha (by simpa only [abelianQuotientConj_mk, ρ, inv_inv, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh)
  let f : T.map π → D := fun q => ⟨ρ q a, hstay q⟩
  have hfree (q : T.map π) (hq : ρ q a = a) : q = 1 := by
    obtain ⟨x, hx, hqx⟩ := q.property
    have hh : x * (a : G) * x⁻¹ = a := by
      have h := congrArg (fun a : A => (a : G)) hq
      rw [← hqx] at h
      exact h
    have hc : Commute x (a : G) := mul_inv_eq_iff_eq_mul.mp hh
    have hxA := centralizer_bound_of_quotient_involution_fixed T L A hT hcover
      hfixed a a.property ha ⟨hx, mem_centralizer_singleton_iff.mpr hc.eq⟩
    apply Subtype.ext
    rw [← hqx]
    exact (QuotientGroup.eq_one_iff x).mpr hxA
  have hf : Function.Injective f := by
    intro q r he
    have hqr : ρ q a = ρ r a := congrArg Subtype.val he
    have hfix : ρ (r⁻¹*q : T.map π) a = a := by
      change ρ ((r : G ⧸ A)⁻¹ * q) a = a
      rw [map_mul, map_inv]
      change (ρ r)⁻¹ (ρ q a) = a
      rw [hqr]
      exact (ρ r).symm_apply_apply a
    exact (inv_mul_eq_one.mp (hfree (r⁻¹*q) hfix)).symm
  have hc : Nat.card D = 8 := by
    let := Fintype.ofFinite A
    have hsub : Nat.card {a : A // (a : G) ∈ L} = 8 := by
      change Nat.card (L.subgroupOf A) = 8
      rw [← inf_subgroupOf_right L A]
      exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans hV
    change Nat.card {a : A // ¬ (a : G) ∈ L} = 8
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hA, hsub]
  have hbij := hf.bijective_of_nat_card_le (by rw [hc]; exact himage.ge)
  obtain ⟨q, hq⟩ := hbij.2 ⟨b,hb⟩
  refine ⟨q, congrArg Subtype.val hq, ?_⟩
  intro r hr
  exact hf (Subtype.ext (hr.trans (congrArg Subtype.val hq).symm))

/-- Involution lifting transports from L/(A∩L) to M/A under M=LA. -/
public theorem involution_lifts_of_normal_supplement
    {M : Type*} [Group M] (L A : Subgroup M) [A.Normal]
    (hcover : L ⊔ A = ⊤)
    (hlift : ∀ q : L ⧸ A.subgroupOf L, orderOf q = 2 →
      ∃ y : L, y^2=1 ∧ QuotientGroup.mk' (A.subgroupOf L) y = q) :
    ∀ q : M ⧸ A, orderOf q = 2 →
      ∃ y ∈ L, y^2=1 ∧ QuotientGroup.mk' A y = q := by
  let f : L →* M ⧸ A := (QuotientGroup.mk' A).comp L.subtype
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective A q
    obtain ⟨y,hy,a,ha,rfl⟩ := mem_sup_of_normal_right.mp (hcover ▸ mem_top x)
    refine ⟨⟨y,hy⟩, ?_⟩
    change QuotientGroup.mk' A y = QuotientGroup.mk' A (y*a)
    have ha' : QuotientGroup.mk' A a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [map_mul,ha',mul_one]
  have hker : A.subgroupOf L = f.ker := by
    ext x
    exact (QuotientGroup.eq_one_iff (x : M)).symm
  let e : (L ⧸ A.subgroupOf L) ≃* M ⧸ A :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  have he (y : L) : e (QuotientGroup.mk' (A.subgroupOf L) y) = QuotientGroup.mk' A y := by
    rfl
  intro q hq
  obtain ⟨y,hy,hyq⟩ := hlift (e.symm q) (e.symm.orderOf_eq q |>.trans hq)
  refine ⟨y,y.property,congrArg Subtype.val hy,?_⟩
  rw [← he,hyq,e.apply_symm_apply]


end Subgroup
