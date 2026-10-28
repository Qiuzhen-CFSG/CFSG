module
public import Theory.GroupTheory.GraphUniquenessSystem.OddIndexRigidity
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.SL2.Affine.Structure
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace
public import Theory.Representation.SL2FourNaturalOrbits.FixedBound

/-!
# Rigidity of the M23-shaped affine edge fixer

An order-48 subgroup containing an elementary sixteen-group other than the
translation group meets the translations in a four-group. The natural
fixed-space bound gives the upper bound; the normalized product order gives
the lower bound. Its image in A₅ has order twelve, so an automorphism fixing
it induces the identity on the quotient. Transitivity on nonzero translations
then fixes the entire core. The odd-index averaging lemma applies to its
index-five join with the core and completes rigidity.

This supplies the pointwise automorphism centralizer in Aschbacher--Smith,
proof of 5.2.10, printed p.657. All placement and order hypotheses are
intrinsic to the specified subgroups; the original source application is in
`RankOneModuleGenericGlobalM23/EdgeRigidity`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23

private theorem rigid_of_transitive_core
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Characteristic] [IsElementaryAbelian 2 N]
    (eQ : (G ⧸ N) ≃* alternatingGroup (Fin 5))
    (hN : Nat.card N = 16) (hH : Nat.card H = 48)
    (hI : Nat.card (N ⊓ H : Subgroup G) = 4)
    (hself : centralizer (N : Set G) ≤ N)
    (htrans : ∀ x y : N, x ≠ 1 → y ≠ 1 → ∃ g : G, g * x * g⁻¹ = y)
    (hfixed : N ⊓ centralizer (H : Set G) = ⊥) :
    GraphUniquenessSystem.AutomorphismRigid H := by
  intro α hα
  have hαH (x : G) (hx : x ∈ H) : α x = x := hα ⟨x,hx⟩
  let π := QuotientGroup.mk' N
  have hc : Nat.card (H.map π) = 12 := by
    have hh := (N.subgroupOf H).card_mul_index
    change Nat.card (N.subgroupOf H) * N.relIndex H = Nat.card H at hh
    have hr : N.relIndex H = Nat.card (H.map π) := by
      simpa only [π,QuotientGroup.ker_mk'] using (relIndex_ker (K := H) π)
    rw [hr] at hh
    have hi : Nat.card (N.subgroupOf H) = 4 := by
      rw [← inf_subgroupOf_right N H,
        Nat.card_congr (subgroupOfEquivOfLe (show N ⊓ H ≤ H from inf_le_right)).toEquiv]
      exact hI
    rw [hi,hH] at hh
    omega
  let aQ := QuotientGroup.congr N N α (characteristic_iff_map_eq.mp inferInstance α)
  have haQ : aQ = MulEquiv.refl _ :=
    AlternatingFiveSubgroupExtension.aut_eq_of_agree
      AlternatingFiveSubgroupExtension.restrictionFaithful eQ (H.map π) hc aQ
      (MulEquiv.refl _) (by
        rintro ⟨q,⟨x,hx,rfl⟩⟩
        change aQ (π x) = π x
        change π (α x) = π x
        rw [hαH x hx])
  have hdis (g : G) : α g * g⁻¹ ∈ N := by
    have hh := congrArg (fun f : MulAut (G ⧸ N) => f (π g)) haQ
    change aQ (π g) = π g at hh
    change π (α g) = π g at hh
    apply (QuotientGroup.eq_one_iff _).mp
    change π (α g * g⁻¹) = 1
    rw [map_mul,map_inv,hh,mul_inv_cancel]
  have hne : N ⊓ H ≠ ⊥ := by intro he; rw [he,card_bot] at hI; omega
  obtain ⟨x,hx,hx1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hx1 : x ≠ 1 := fun hh => hx1 (by simp [hh])
  have hfixN (y : N) : α y = y := by
    by_cases hy : y = 1
    · simp [hy]
    obtain ⟨g,hg⟩ := htrans ⟨x,hx.1⟩ y (fun he => hx1 (congrArg Subtype.val he)) hy
    have hcomm : Commute (α g * g⁻¹) (y:G) :=
      setLike_mul_comm (hdis g) y.property
    have he : α (g * x * g⁻¹) = (α g * g⁻¹) * (g*x*g⁻¹) * (α g*g⁻¹)⁻¹ := by
      rw [map_mul,map_mul,map_inv,hαH x hx.2]
      group
    rw [hg] at he
    rw [he, hcomm.eq, mul_inv_cancel_right]
  have hcardQ : Nat.card (G ⧸ N) = 60 := by
    rw [Nat.card_congr eQ.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hcardG : Nat.card G = 960 := by
    rw [←N.card_mul_index,index_eq_card,hN,hcardQ]
  have hcardS : Nat.card (N ⊔ H : Subgroup G) = 192 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes N H
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hN,hH,hI] at hh
    omega
  have hiS : Odd (N ⊔ H : Subgroup G).index := by
    have hh := (N ⊔ H : Subgroup G).card_mul_index
    rw [hcardS,hcardG] at hh
    have hi : (N ⊔ H : Subgroup G).index = 5 := by omega
    rw [hi]; decide
  have hfS : N ⊓ centralizer ((N ⊔ H : Subgroup G) : Set G) = ⊥ := by
    apply le_bot_iff.mp
    calc
      _ ≤ N ⊓ centralizer (H : Set G) :=
        inf_le_inf_left _ (centralizer_le (show (H : Set G) ⊆ (N ⊔ H : Subgroup G) from fun _ => mem_sup_right))
      _ = ⊥ := hfixed
  apply GraphUniquenessSystem.automorphismRigid_of_odd_index N (N ⊔ H) le_sup_left
    hself (fun n => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 N) n) hiS hfS α
  intro j
  have hle : N ⊔ H ≤ α.toMonoidHom.eqLocus (MonoidHom.id G) := by
    apply sup_le
    · intro y hy; exact hfixN ⟨y,hy⟩
    · intro y hy; exact hαH y hy
  exact hle j.property

open Representation.SL2FourNatural

/-- An order-48 subgroup meeting the natural two-core in a four-group
is an automorphism determining subgroup of the special affine group. -/
theorem affine_four_order48_rigid
    (H : Subgroup (Matrix.SL2.Affine F))
    (hH : Nat.card H = 48)
    (hI : Nat.card (Matrix.SL2.translations F ⊓ H : Subgroup (Matrix.SL2.Affine F)) = 4) :
    GraphUniquenessSystem.AutomorphismRigid H := by
  let N := Matrix.SL2.translations F
  let : N.Characteristic := by
    change (Matrix.SL2.translations F).Characteristic
    rw [← Matrix.SL2.affine_twoCore_eq]
    infer_instance
  have hN : Nat.card N = 16 := by
    rw [← Nat.card_congr (Matrix.SL2.translationsEquiv F).toEquiv]
    change Nat.card V = 16
    rw [Nat.card_eq_fintype_card,card_vector]
  let eQ := (Matrix.SL2.quotientTranslationsEquiv F).trans alternatingFiveEquiv
  apply rigid_of_transitive_core N H eQ hN hH hI
    (Matrix.SL2.centralizer_translations_eq F).le
  · intro x y hx hy
    let v := (Matrix.SL2.translationsEquiv F).symm x
    let w := (Matrix.SL2.translationsEquiv F).symm y
    have hv : v.toAdd ≠ 0 := by
      intro hv
      have he : v = 1 := Multiplicative.toAdd.injective hv
      exact hx ((Matrix.SL2.translationsEquiv F).symm.injective (he.trans (map_one _).symm))
    have hw : w.toAdd ≠ 0 := by
      intro hw
      have he : w = 1 := Multiplicative.toAdd.injective hw
      exact hy ((Matrix.SL2.translationsEquiv F).symm.injective (he.trans (map_one _).symm))
    obtain ⟨g,hg⟩ := transitive_nonzero v.toAdd w.toAdd hv hw
    have hxv : (x : Matrix.SL2.Affine F) = SemidirectProduct.inl v := by
      exact congrArg Subtype.val ((Matrix.SL2.translationsEquiv F).apply_symm_apply x).symm
    have hyw : (y : Matrix.SL2.Affine F) = SemidirectProduct.inl w := by
      exact congrArg Subtype.val ((Matrix.SL2.translationsEquiv F).apply_symm_apply y).symm
    refine ⟨SemidirectProduct.inr g,?_⟩
    rw [hxv,hyw,Matrix.SL2.conjugate_inl]
    exact congrArg SemidirectProduct.inl (Multiplicative.toAdd.injective hg)
  · obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (by rw [hH]; norm_num)
    have hbG : orderOf (b : Matrix.SL2.Affine F) = 3 :=
      (orderOf_injective H.subtype H.subtype_injective b).trans hb
    have hr3 : b.val.right ^ 3 = 1 := by
      exact congrArg SemidirectProduct.right (hbG ▸ pow_orderOf_eq_one b.val)
    have hr1 : b.val.right ≠ 1 := by
      intro hh
      have hm : b.val ∈ N := hh
      have hp : b.val ^ 2 = 1 := by
        exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 N) (⟨b.val,hm⟩ : N))
      have hd := orderOf_dvd_of_pow_eq_one hp
      rw [hbG] at hd
      norm_num at hd
    have hr : orderOf b.val.right = 3 := orderOf_eq_prime hr3 hr1
    apply eq_bot_iff.mpr
    rintro x ⟨hx,hc⟩
    have hxR : x.right = 1 := hx
    have hh := congrArg SemidirectProduct.left (mem_centralizer_iff.mp hc b.val b.property)
    have hfix : action b.val.right x.left.toAdd = x.left.toAdd := by
      change b.val.left * Matrix.SL2.naturalAction F b.val.right x.left =
        x.left * Matrix.SL2.naturalAction F x.right b.val.left at hh
      rw [hxR,map_one,MulAut.one_apply,mul_comm x.left] at hh
      exact congrArg Multiplicative.toAdd (mul_left_cancel hh)
    have hz := cubic_fixed_eq_zero b.val.right hr x.left.toAdd hfix
    apply mem_bot.mpr
    apply SemidirectProduct.ext
    · exact Multiplicative.toAdd.injective hz
    · exact hxR

private theorem affine_four_core_intersection
    (U : Subgroup (Matrix.SL2.Affine F)) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) (hne : U ≠ Matrix.SL2.translations F) :
    Nat.card (Matrix.SL2.translations F ⊓ U : Subgroup (Matrix.SL2.Affine F)) = 4 := by
  let N := Matrix.SL2.translations F
  have hN : Nat.card N = 16 := by
    rw [← Nat.card_congr (Matrix.SL2.translationsEquiv F).toEquiv]
    change Nat.card V = 16
    rw [Nat.card_eq_fintype_card,card_vector]
  have hcG : Nat.card (Matrix.SL2.Affine F) = 960 := by
    rw [SemidirectProduct.card]
    have hs : Nat.card SL = 60 := by
      rw [Nat.card_congr alternatingFiveEquiv.toEquiv,nat_card_alternatingGroup]
      norm_num
    change Nat.card V * Nat.card SL = _
    rw [Nat.card_eq_fintype_card (α := V),card_vector,hs]
  have hnot : ¬ U ≤ N := fun hu => hne (eq_of_le_of_card_ge hu (by rw [hN,hU]))
  obtain ⟨u,hu,huN⟩ := Set.not_subset.mp hnot
  have hur : u.right ≠ 1 := huN
  have hfx (x : (N ⊓ U : Subgroup (Matrix.SL2.Affine F))) : action u.right x.val.left.toAdd = x.val.left.toAdd := by
    have hh := congrArg SemidirectProduct.left (setLike_mul_comm hu x.property.2)
    have hxR : x.val.right = 1 := x.property.1
    change u.left * Matrix.SL2.naturalAction F u.right x.val.left =
      x.val.left * Matrix.SL2.naturalAction F x.val.right u.left at hh
    rw [hxR,map_one,MulAut.one_apply,mul_comm x.val.left] at hh
    exact congrArg Multiplicative.toAdd (mul_left_cancel hh)
  let f : (N ⊓ U : Subgroup (Matrix.SL2.Affine F)) →
      (action u.right).toLinearMap.fixedSubmodule := fun x => ⟨x.val.left.toAdd,hfx x⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Multiplicative.toAdd.injective (congrArg Subtype.val he)
    · exact (show x.val.right = 1 from x.property.1).trans
        (show y.val.right = 1 from y.property.1).symm
  have hb : Nat.card (N ⊓ U : Subgroup (Matrix.SL2.Affine F)) ≤ 4 :=
    (Nat.card_le_card_of_injective f hf).trans
      (normalizer_nonidentity_fixed_card_le_four (action u.right)
        (Subgroup.le_normalizer ⟨u.right,rfl⟩)
        (fun he => hur (action_faithful (he.trans action.map_one.symm))))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes N U
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hN,hU] at hc
  have hd : Nat.card (N ⊔ U : Subgroup (Matrix.SL2.Affine F)) ∣ 64 := by
    have h₁ : Nat.card (N ⊔ U : Subgroup (Matrix.SL2.Affine F)) ∣ 256 :=
      ⟨Nat.card (N ⊓ U : Subgroup (Matrix.SL2.Affine F)),by nlinarith [hc]⟩
    have h₂ := card_subgroup_dvd_card (N ⊔ U : Subgroup (Matrix.SL2.Affine F))
    rw [hcG] at h₂
    exact Nat.dvd_gcd h₁ h₂
  have hle := Nat.le_of_dvd (by decide : 0 < 64) hd
  nlinarith

/-- The actual elementary sixteen-group distinct from translations makes an
order-48 overgroup rigid, without a choice of affine coordinates on that subgroup. -/
theorem affine_four_elementary_overgroup_rigid
    (H U : Subgroup (Matrix.SL2.Affine F)) [IsElementaryAbelian 2 U]
    (hH : Nat.card H = 48) (hU : Nat.card U = 16) (hUH : U ≤ H)
    (hne : U ≠ Matrix.SL2.translations F) :
    GraphUniquenessSystem.AutomorphismRigid H := by
  let N := Matrix.SL2.translations F
  have hU' : Nat.card (U.subgroupOf H) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).trans hU
  have hiU : (U.subgroupOf H).index = 3 := by
    have hh := (U.subgroupOf H).card_mul_index
    rw [hU',hH] at hh
    omega
  let P : Sylow 2 H := (IsPGroup.of_card (show Nat.card (U.subgroupOf H) = 2^4 from hU')).toSylow
    (by rw [hiU]; decide)
  have hnP : N.subgroupOf H ≤ P :=
    ((Matrix.SL2.translations_isPGroup F).comap_of_injective H.subtype H.subtype_injective).le_sylow_of_normal P
  have hi : N ⊓ H = N ⊓ U := by
    apply le_antisymm
    · rintro x ⟨hxN,hxH⟩
      exact ⟨hxN,hnP (show (⟨x,hxH⟩ : H) ∈ N.subgroupOf H from hxN)⟩
    · exact inf_le_inf_left _ hUH
  exact affine_four_order48_rigid H hH (hi ▸ affine_four_core_intersection U hU hne)

/-- Transport the rigidity criterion to a marked copy of the special affine group. -/
theorem rigid_of_affine_four_elementary_overgroup
    {G : Type*} [Group G] (e : G ≃* Matrix.SL2.Affine F)
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hH : Nat.card H = 48) (hU : Nat.card U = 16) (hUH : U ≤ H)
    (hne : U ≠ pCore 2 G) : GraphUniquenessSystem.AutomorphismRigid H := by
  let : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hne' : U.map e.toMonoidHom ≠ Matrix.SL2.translations F := by
    intro hh
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso,Matrix.SL2.affine_twoCore_eq,hh]
  let : IsElementaryAbelian 2 (U.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hr := affine_four_elementary_overgroup_rigid (H.map e.toMonoidHom)
    (U.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hH)
    ((card_map_of_injective e.injective).trans hU) (map_mono hUH) hne'
  intro α hα
  have hh : MulAut.congr e α = MulEquiv.refl _ := hr _ (by
    rintro ⟨x,⟨y,hy,rfl⟩⟩
    change e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply,hα ⟨y,hy⟩])
  apply (MulAut.congr e).injective
  change (MulAut.congr e) α = (MulAut.congr e) 1
  rw [map_one]
  exact hh

end Theory.GroupTheory.QuasithinM23
