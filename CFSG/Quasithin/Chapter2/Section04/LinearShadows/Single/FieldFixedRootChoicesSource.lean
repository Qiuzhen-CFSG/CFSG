module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionRootSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.RootQuotientCoordinatesSource
public import Theory.GroupTheory.ElementaryFixedQuotientLifting
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InsideFieldFusionSource

/-!
# Fixed representatives in the actual root quotient

The proved square-root fixed counts on O₂(H) and R/O₂(H) let fixed quotient
elements lift to fixed representatives in R. The source quotient has order
2^n, so there is a nonzero fixed choice, and two distinct nonzero choices
unless n=2. Conjugation inside R transports these choices from a marked
field involution to every involution of S outside R.

This supplies the root parameters in the actual fixed-commutator and
small-field alternative of Aschbacher–Smith, 2.4.12(2) and 2.4.21,
printed pp.532 and 536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Nonzero fixed representatives for the marked field-complement involution. -/
theorem source_field_fixed_root_choices
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
    ∃ r : R, α r=r ∧ QuotientGroup.mk' N r≠1 ∧
      (n=2 ∨ ∃ t : R, α t=t ∧ QuotientGroup.mk' N t≠1 ∧
        QuotientGroup.mk' N t≠QuotientGroup.mk' N r) := by
  classical
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
  change ∃ r : R, α r=r ∧ QuotientGroup.mk' N r≠1 ∧
      (n=2 ∨ ∃ t : R, α t=t ∧ QuotientGroup.mk' N t≠1 ∧
        QuotientGroup.mk' N t≠QuotientGroup.mk' N r)
  let : IsElementaryAbelian 2 N :=
    (source_field_elementary_layers d hG T hST hsingle hL hM hTM hunique c).1
  have hcN := source_field_involution_core_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2
  have hα : Function.Involutive α := by
    intro r
    apply Subtype.ext
    change s*(s*(r:G)*s⁻¹)*s⁻¹=(r:G)
    have hss : s*s=1 := by simpa only [←pow_two,hs2] using pow_orderOf_eq_one s
    have hinv : s⁻¹=s := inv_eq_of_mul_eq_one_left hss
    rw [hinv]
    calc
      s*(s*(r:G)*s)*s=(s*s)*(r:G)*(s*s) := by group
      _=(r:G) := by rw [hss,one_mul,mul_one]
  let C := (QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))
  have hc : Nat.card C ^ 2=2^n :=
    (source_field_involution_sylow_quotient_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2).trans
      (source_root_quotient_card d hG T hST hsingle hL hM hTM hunique)
  have hfour : 4≤2^n := by
    have hn := hL.1
    calc
      4=2^2 := rfl
      _≤2^n := pow_le_pow_right₀ (by norm_num) (by omega)
  have hc1 : 1<Nat.card C := by nlinarith
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨v,hv⟩ := Fintype.exists_ne_of_one_lt_card (by simpa only [Nat.card_eq_fintype_card] using hc1) (1:C)
  obtain ⟨r,hr,her⟩ := Theory.GroupTheory.exists_fixed_quotient_lift_of_elementary_kernel
    N α hα hN hcN v.val v.property
  have hv1 : (v:R ⧸ N)≠1 := fun he=>hv (Subtype.ext he)
  refine ⟨r,hr,(by rw [her]; exact hv1),?_⟩
  by_cases hn : n=2
  · exact Or.inl hn
  · apply Or.inr
    have height : 8≤2^n := by
      have hn' := hL.1
      calc
        8=2^3 := rfl
        _≤2^n := pow_le_pow_right₀ (by norm_num) (by omega)
    have hc2 : 2<Fintype.card C := by
      rw [←Nat.card_eq_fintype_card]
      nlinarith
    obtain ⟨w,_,hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({1,v}:Finset C).card<Finset.univ.card from (Finset.card_le_two).trans_lt (by simpa only [Finset.card_univ] using hc2))
    have hw1 : w≠1 := fun he=>hw (by simp [he])
    have hwv : w≠v := fun he=>hw (by simp [he])
    obtain ⟨t,ht,het⟩ := Theory.GroupTheory.exists_fixed_quotient_lift_of_elementary_kernel
      N α hα hN hcN w.val w.property
    refine ⟨t,ht,?_,?_⟩
    · rw [het]
      exact fun he=>hw1 (Subtype.ext he)
    · rw [het,her]
      exact fun he=>hwv (Subtype.ext he)

/-- Fixed nonzero root choices for every actual inside involution. -/
theorem source_inside_fixed_root_choices
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (a : G) (haS : a ∈ (d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    let α := (R.normalizerMonoidHom ⟨a,source_field_actor_normalizes_thompson d a haS⟩).toMonoidHom
    ∃ r : R, α r=r ∧ QuotientGroup.mk' N r≠1 ∧
      (n=2 ∨ ∃ t : R, α t=t ∧ QuotientGroup.mk' N t≠1 ∧
        QuotientGroup.mk' N t≠QuotientGroup.mk' N r) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  let α := (R.normalizerMonoidHom ⟨a,source_field_actor_normalizes_thompson d a haS⟩).toMonoidHom
  change ∃ r : R, α r=r ∧ QuotientGroup.mk' N r≠1 ∧
      (n=2 ∨ ∃ t : R, α t=t ∧ QuotientGroup.mk' N t≠1 ∧
        QuotientGroup.mk' N t≠QuotientGroup.mk' N r)
  have ha1 : a≠1 := fun he=>haR (he ▸ one_mem R)
  obtain ⟨s,hs,hs2,k,hk,hka⟩ := source_inside_involution_conj_field d hG T hST hsingle hL
    hM hTM hunique c a haS (orderOf_eq_prime ha2 ha1) haR
  let β := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let e := MulAut.conj (⟨k,hk⟩ : R)
  let q := QuotientGroup.mk' N
  let f := MulAut.conj (q ⟨k,hk⟩)
  have heq (r:R) : q (e r)=f (q r) := by
    change q (⟨k,hk⟩*r*⟨k,hk⟩⁻¹)=q ⟨k,hk⟩*q r*(q ⟨k,hk⟩)⁻¹
    rw [map_mul,map_mul,map_inv]
  have hefix (r:R) (hr:β r=r) : α (e r)=e r := by
    apply Subtype.ext
    have hh := congrArg Subtype.val hr
    change s*(r:G)*s⁻¹=(r:G) at hh
    change a*(k*(r:G)*k⁻¹)*a⁻¹=k*(r:G)*k⁻¹
    calc
      a*(k*(r:G)*k⁻¹)*a⁻¹=k*(s*(r:G)*s⁻¹)*k⁻¹ := by rw [←hka];group
      _=k*(r:G)*k⁻¹ := by rw [hh]
  obtain ⟨r,hr,hr1,ht⟩ := source_field_fixed_root_choices d hG T hST hsingle hL hM hTM hunique c s hs hs2
  have hn1 (r:R) (hr:q r≠1) : q (e r)≠1 := by
    rw [heq]
    exact fun he=>hr (f.injective (he.trans f.map_one.symm))
  refine ⟨e r,hefix r hr,hn1 r hr1,?_⟩
  rcases ht with hn | ⟨t,ht,ht1,htr⟩
  · exact Or.inl hn
  · refine Or.inr ⟨e t,hefix t ht,hn1 t ht1,?_⟩
    rw [heq,heq]
    exact fun he=>htr (f.injective he)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
