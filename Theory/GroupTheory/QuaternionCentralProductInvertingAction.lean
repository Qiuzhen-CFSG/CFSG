module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition
public import Theory.GroupTheory.QuaternionCentralProductNineAction.NonInversion
public import Theory.SpecificGroups.SL2.ThreeCharacteristicTwo

/-!
# Inverting actions and normal SL₂(3) factors

For a self-centralizing quaternion central product with quotient of order
eighteen, construct the two independent cubic actors and their actual SL₂(3)
extensions. An actor inverting the cubic quotient cannot interchange the
quaternion factors. If it generates the ambient group with the two-residual,
both quaternion factors are normal. Each SL₂(3) extension is the centralizer
of the opposite quaternion factor inside the residual, so it too is normal.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the final local
construction in the proof of Theorem 14.4.3, printed p.1008. This is the
intrinsic factor calculation; it does not prove the earlier local eliminations
or the ambient G₂(3) recognition theorem.
-/

open scoped Pointwise

namespace Subgroup

/-- Inversion on the cubic quotient preserves both actual quaternion factors. -/
public theorem QuaternionIndependentCubics.normalizes_factors_of_quotient_inversion
    {G D : Type*} [Group G] [Finite G] [Group D]
    {B C : Subgroup G} (actors : QuaternionIndependentCubics B C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (f : G →* D) (hker : f.ker = B ⊔ C)
    (s : G) (hn : s ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hinv : ∀ a : actors.A, f s * f a * (f s)⁻¹ = (f a)⁻¹) :
    s ∈ normalizer (B : Set G) ∧ s ∈ normalizer (C : Set G) := by
  let e := MulAut.conj s
  have hj : (B ⊔ C).map e.toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have him (E : Subgroup G) (hE : Nonempty (E ≃* QuaternionGroup 2))
      (hle : E ≤ B ⊔ C) : E.map e.toMonoidHom = B ∨ E.map e.toMonoidHom = C :=
    quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
      ⟨(E.equivMapOfInjective e.toMonoidHom e.injective).symm.trans hE.some⟩
      ((map_mono hle).trans_eq hj)
  have hCC : C.map e.toMonoidHom = C := by
    rcases him C hC le_sup_right with hCB | hCC
    · obtain ⟨a, ha⟩ := actors.not_inversion_of_factor_swap hB hcomm f hker s hCB
      exact (ha (hinv a)).elim
    · exact hCC
  have hne : B ≠ C := by
    intro h
    have hc : Nat.card B = 8 := by
      rw [Nat.card_congr hB.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← h, inf_idem, hc] at hinter
    omega
  have hBB : B.map e.toMonoidHom = B :=
    (him B hB le_sup_left).resolve_right
      (fun hBC => hne (map_injective e.injective (hBC.trans hCC.symm)))
  exact ⟨mem_normalizer_iff_map_conj_eq.mpr hBB,
    mem_normalizer_iff_map_conj_eq.mpr hCC⟩

private theorem commuting_factor_eq_centralizer_inf
    {G : Type*} [Group G] [Finite G]
    (B C L R : Subgroup G)
    (hBC : B ⊓ C = (center C).map C.subtype)
    (hBL : B ≤ L) (hCR : C ≤ R)
    (hcomm : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l)
    (hR : Nonempty (R ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hcore : (pCore 2 R).map R.subtype = C) :
    L = (L ⊔ R) ⊓ centralizer (C : Set G) := by
  have hLC : L ≤ centralizer (C : Set G) :=
    fun l hl c hc => (hcomm l hl c (hCR hc)).symm
  apply le_antisymm (le_inf le_sup_left hLC)
  intro z hz
  have hn : L ≤ normalizer (R : Set G) :=
    (show L ≤ centralizer (R : Set G) from
      fun l hl r hr => (hcomm l hl r hr).symm).trans (centralizer_le_normalizer _)
  have hzj : z ∈ (L : Set G) * (R : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right L R hn]
    exact hz.1
  obtain ⟨l, hl, r, hr, rfl⟩ := hzj
  have hrC : r ∈ centralizer (C : Set G) := by
    have ht := (centralizer (C : Set G)).mul_mem
      ((centralizer (C : Set G)).inv_mem (hLC hl)) hz.2
    simpa only [inv_mul_cancel_left] using ht
  have hself : centralizer (pCore 2 R : Set R) ≤ pCore 2 R :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 hR.some).mpr
      Matrix.SpecialLinearGroup.three_twoCore_self_centralizing
  have hrCore : (⟨r, hr⟩ : R) ∈ pCore 2 R := by
    apply hself
    intro c hc
    apply Subtype.ext
    exact hrC c (hcore ▸ mem_map_of_mem R.subtype hc)
  have hrCmem : r ∈ C := hcore ▸ mem_map_of_mem R.subtype hrCore
  have hrZ : (⟨r, hrCmem⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact hrC c c.property
  have hrB : r ∈ B := by
    have hm : r ∈ (center C).map C.subtype := ⟨⟨r, hrCmem⟩, hrZ, rfl⟩
    rw [← hBC] at hm
    exact hm.1
  exact L.mul_mem hl (hBL hrB)

/-- The factors of the recognized residual are its centralizers of the opposite
quaternion factors. This identifies their embeddings, not only their types. -/
public theorem QuaternionResidualCentralProduct.centralizer_descriptions
    {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} {d : QuaternionCentralProductData Q}
    (c : QuaternionResidualCentralProduct Q d) :
    c.left = pResidual 2 G ⊓ centralizer (d.right.map Q.subtype : Set G) ∧
    c.right = pResidual 2 G ⊓ centralizer (d.left.map Q.subtype : Set G) := by
  have hB : Nonempty (d.left.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
  have hC : Nonempty (d.right.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
  have hi : Nat.card (d.left.map Q.subtype ⊓ d.right.map Q.subtype : Subgroup G) = 2 := by
    rw [← map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective, d.intersection_card]
  have hc : ∀ b ∈ d.left.map Q.subtype, ∀ r ∈ d.right.map Q.subtype, b*r=r*b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (d.commute b hb r hr)
  constructor
  · rw [← c.span]
    exact commuting_factor_eq_centralizer_inf _ _ _ _
      (by simpa only [inf_comm] using (intersection_eq_factor_center _ _ hC
        (by simpa only [inf_comm] using hi) (fun r hr b hb => (hc b hb r hr).symm)))
      c.left_contains c.right_contains c.commute c.right_model c.right_core
  · rw [← c.span, sup_comm]
    exact commuting_factor_eq_centralizer_inf _ _ _ _
      (by simpa only [inf_comm] using (intersection_eq_factor_center _ _ hB hi hc))
      c.right_contains c.left_contains (fun r hr l hl => (c.commute l hl r hr).symm)
      c.left_model c.left_core

/-- Preserving the quaternion factors makes the actual SL₂(3) factors normal. -/
public theorem QuaternionResidualCentralProduct.normal_factors
    {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} {d : QuaternionCentralProductData Q}
    (c : QuaternionResidualCentralProduct Q d)
    [ (d.left.map Q.subtype).Normal ] [ (d.right.map Q.subtype).Normal ] :
    c.left.Normal ∧ c.right.Normal := by
  rw [c.centralizer_descriptions.1, c.centralizer_descriptions.2]
  exact ⟨inferInstance, inferInstance⟩

/-- A quaternion core with quotient of order eighteen and an inverting
generator has two normal SL₂(3) residual factors. The cubic actors and the
factors themselves are constructed, not supplied as recognition data. -/
public theorem normal_residual_factors_of_quaternion_inverting_quotient
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q) (hindex : Q.index = 18)
    (s : G) (hgen : pResidual 2 G ⊔ zpowers s = ⊤)
    (hinv : ∀ k : pResidual 2 G,
      QuotientGroup.mk' Q (s * k * s⁻¹) = (QuotientGroup.mk' Q k)⁻¹) :
    ∃ c : QuaternionResidualCentralProduct Q d,
      c.left.Normal ∧ c.right.Normal ∧ (c.left ⊔ c.right).index = 2 := by
  have hG : Nat.card G = 576 := by
    have hc := Q.card_mul_index
    rw [d.card, hindex] at hc
    exact hc.symm
  obtain ⟨actors⟩ := independent_cubics_of_normal_quaternion_product_card_576
    Q d hcentral hG
  obtain ⟨c, hL, hR⟩ := actors.residual_central_product Q d hG
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  have hj : B ⊔ C = Q := by
    change d.left.map Q.subtype ⊔ d.right.map Q.subtype = Q
    rw [← map_sup, d.span]
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, mem_top _, rfl⟩⟩
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
  have hC : Nonempty (C ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
  have hi : Nat.card (B ⊓ C : Subgroup G) = 2 := by
    change Nat.card (d.left.map Q.subtype ⊓ d.right.map Q.subtype : Subgroup G) = 2
    rw [← map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective, d.intersection_card]
  have hc : ∀ b ∈ B, ∀ r ∈ C, b*r=r*b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (d.commute b hb r hr)
  have hKA : pResidual 2 G = Q ⊔ actors.A := by
    calc
      pResidual 2 G = (B ⊔ zpowers (actors.x : G)) ⊔
          (C ⊔ zpowers (actors.y : G)) := by rw [← c.span, hL, hR]
      _ = (B ⊔ C) ⊔ (zpowers (actors.x : G) ⊔ zpowers (actors.y : G)) := by ac_rfl
      _ = Q ⊔ actors.A := congrArg₂ (· ⊔ ·) hj actors.generated
  have hAK : actors.A ≤ pResidual 2 G := by rw [hKA]; exact le_sup_right
  have hs := actors.normalizes_factors_of_quotient_inversion hB hC hi hc (QuotientGroup.mk' Q)
    (by rw [QuotientGroup.ker_mk', hj]) s
    (by rw [hj, Q.normalizer_eq_top]; trivial)
    (fun a => by simpa only [map_mul, map_inv] using hinv ⟨a, hAK a.property⟩)
  have hnorm (D E : Subgroup G) (hDE : D ⊔ E = Q)
      (hED : ∀ e ∈ E, ∀ b ∈ D, b*e=e*b)
      (hAD : actors.A ≤ normalizer (D : Set G))
      (hsD : s ∈ normalizer (D : Set G)) : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen, hKA]
    have hQD : Q ≤ normalizer (D : Set G) := hDE ▸ sup_le D.le_normalizer
      ((show E ≤ centralizer (D : Set G) from hED).trans (centralizer_le_normalizer _))
    exact sup_le (sup_le hQD hAD) (zpowers_le.mpr hsD)
  let : B.Normal := hnorm B C hj (fun r hr b hb => hc b hb r hr)
    actors.normalizes_left hs.1
  let : C.Normal := hnorm C B (by rw [sup_comm, hj])
    (fun b hb r hr => (hc b hb r hr).symm) actors.normalizes_right hs.2
  obtain ⟨hnL, hnR⟩ := c.normal_factors
  have hcard := actors.extensions_product Q d hG
  have hcardL : Nat.card c.left = 24 := by rw [hL]; exact hcard.1
  have hcardR : Nat.card c.right = 24 := by rw [hR]; exact hcard.2.1
  have hcardI : Nat.card (c.left ⊓ c.right : Subgroup G) = 2 := by
    rw [c.intersection, card_map_of_injective Q.subtype_injective, d.center_card]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes c.left c.right
    ((show c.right ≤ centralizer (c.left : Set G) from
      fun r hr l hl => c.commute l hl r hr).trans (centralizer_le_normalizer _))
  have hix := (c.left ⊔ c.right).card_mul_index
  rw [hcardL, hcardR, hcardI] at hprod
  rw [hG] at hix
  refine ⟨c, hnL, hnR, ?_⟩
  have hcardJoin : Nat.card (c.left ⊔ c.right : Subgroup G) = 288 := by omega
  rw [hcardJoin] at hix
  omega

end Subgroup
