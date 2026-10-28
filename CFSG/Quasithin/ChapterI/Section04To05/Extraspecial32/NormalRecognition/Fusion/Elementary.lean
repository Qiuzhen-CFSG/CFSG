module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Defs
public import Theory.GroupTheory.PGroup.ExtraspecialInvolutionCosetAction
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Elementary closure of the seven-element core fusion set

Assume exactly seven elements of the extraspecial core are ambient conjugates
of the distinguished involution. A generator of the Sylow three-subgroup fixes
precisely the center of the core, and its action on the central quotient has no
nonidentity fixed point: an order-three permutation of a two-element central
fiber is trivial. The product of the three points in a cubic orbit is therefore
one, so a noncentral fused involution supplies a plane in the central quotient.

Every nonidentity element of the full preimage of this plane is fused to the
distinguished involution, since a noncentral central coset is one inner conjugacy
class. Its order is eight. The seven-element premise identifies its underlying
set with the fusion set with identity adjoined; the literal generated subgroup
thus has exponent dividing two and is elementary abelian.

This is the conditional elementary-closure input to
`Hypotheses.fusionEightData_of_seven_of_elementary`. The separate fusion count
remains explicit. No ambient normality or quaternion-factor normality is used.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, §2 and the opening proof of Lemma 4.1;
Aschbacher–Smith, I.4.6, `refs/quasithin.pdf`, printed p.417.
-/

open Subgroup
open scoped IsMulCommutative


private theorem cubic_quotient_fixed {Q : Type*} [Group Q] [IsExtraspecial 2 Q]
    (f : MulAut Q) (hf3 : ∀ x, f (f (f x)) = x)
    (hfix : ∀ x, f x = x ↔ x ∈ center Q)
    {x : Q} (hx : QuotientGroup.mk' (center Q) (f x) = QuotientGroup.mk' (center Q) x) :
    x ∈ center Q := by
  let d := x⁻¹ * f x
  have hd : d ∈ center Q := QuotientGroup.eq.mp hx.symm
  have hd2 : d ^ 2 = 1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d, hd⟩ : center Q)))
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one,
      IsExtraspecial.center_order_p 2 Q] using hh
  have hdFix : f d = d := (hfix d).mpr hd
  have hfx : f x = x * d := by simp [d]
  have hd3 : d ^ 3 = 1 := by
    have hh := hf3 x
    simp only [map_mul, hfx, hdFix] at hh
    have : x * d ^ 3 = x * 1 := by simpa only [pow_succ, pow_zero, one_mul,
      mul_one, mul_assoc] using hh
    exact mul_left_cancel this
  have hd1 : d = 1 := by simpa only [pow_succ, hd2, one_mul] using hd3
  apply (hfix x).mp
  simpa only [hd1, mul_one] using hfx

private theorem cubic_norm {Q : Type*} [Group Q] [IsExtraspecial 2 Q]
    (f : MulAut Q) (hf3 : ∀ x, f (f (f x)) = x)
    (hfix : ∀ x, f x = x ↔ x ∈ center Q) (x : Q) :
    QuotientGroup.mk' (center Q) (x * f x * f (f x)) = 1 := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    IsExtraspecial.quotient_elementary_abelian 2 Q
  apply (QuotientGroup.eq_one_iff _).mpr
  apply cubic_quotient_fixed f hf3 hfix
  simp only [map_mul, hf3]
  ac_rfl

namespace CFSG.Quasithin.Extraspecial32.Hypotheses
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem cubic_action (h : Hypotheses z) :
    ∃ f : MulAut (Core z), (∀ x, f (f (f x)) = x) ∧
      (∀ x, f x = x ↔ x ∈ center (Core z)) ∧
      (∀ x : Core z, IsConj ((x : Centralizer z) : G) ((f x : Centralizer z) : G)) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic h.X := isCyclic_of_prime_card h.sylow_three_card
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := h.X)
  let f : MulAut (Core z) := MulAut.conjNormal (a : Centralizer z)
  have ha3 : a ^ 3 = 1 := by
    simpa only [h.sylow_three_card] using pow_card_eq_one' (x := a)
  have hf3 : f ^ 3 = 1 := by
    change (MulAut.conjNormal (H := Core z) (a : Centralizer z)) ^ 3 = 1
    rw [← map_pow, ← Subgroup.coe_pow, ha3, OneMemClass.coe_one, map_one]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    have he := DFunLike.congr_fun hf3 x
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using he
  · intro x
    constructor
    · intro hx
      have hax : Commute (a : Centralizer z) (x : Centralizer z) :=
        mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx)
      have hxfix : (x : Centralizer z) ∈ centralizer (h.X : Set (Centralizer z)) := by
        intro b hb
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha ⟨b, hb⟩)
        have hn' : (a : Centralizer z) ^ n = b := congrArg Subtype.val hn
        rw [← hn']
        exact (hax.zpow_left n).eq
      have hxline : (x : Centralizer z) ∈ zpowers (distinguished z) :=
        h.fixed ▸ (show (x : Centralizer z) ∈ Core z ⊓ centralizer (h.X : Set (Centralizer z))
          from ⟨x.property, hxfix⟩)
      rw [← h.core_center_image] at hxline
      obtain ⟨y, hy, hyx⟩ := hxline
      exact (Subtype.ext hyx : y = x) ▸ hy
    · intro hx
      have hxline : (x : Centralizer z) ∈ zpowers (distinguished z) :=
        h.core_center_image ▸ mem_map_of_mem (Core z).subtype hx
      rw [← h.fixed] at hxline
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hxline.2 a a.property)
  · intro x
    exact isConj_iff.mpr ⟨((a : Centralizer z) : G), rfl⟩

/-- Seven conjugates in the literal core generate an elementary abelian subgroup.
The fusion-count premise is supplied separately by the source fusion analysis. -/
public theorem fusionCore_elementary_of_seven (h : Hypotheses z)
    (hs : Nat.card {x : G // x ∈ coreInG z ∧ IsConj z x} = 7) :
    IsElementaryAbelian 2 (fusionCore z) := by
  classical
  let : IsExtraspecial 2 (Core z) := h.extraspecial
  let : IsElementaryAbelian 2 (Core z ⧸ center (Core z)) :=
    IsExtraspecial.quotient_elementary_abelian 2 (Core z)
  let i : Core z →* G := (Centralizer z).subtype.comp (Core z).subtype
  have hi : Function.Injective i :=
    (Centralizer z).subtype_injective.comp (Core z).subtype_injective
  let t : Core z := ⟨distinguished z, h.distinguished_mem_core⟩
  have hz1 : z ≠ 1 := by
    intro hz
    have hh := h.involution
    simp [hz] at hh
  have htZ : t ∈ center (Core z) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.val.property
  have ht1 : t ≠ 1 := fun ht => hz1 (congrArg i ht)
  have hcenter (u : Core z) (hu : u ∈ center (Core z)) : u = 1 ∨ u = t := by
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    right
    obtain ⟨v, _, hv⟩ := (Nat.card_eq_two_iff' (1 : center (Core z))).mp
      (IsExtraspecial.center_order_p 2 (Core z))
    have hu' : (⟨u, hu⟩ : center (Core z)) ≠ 1 := fun he => hu1 (congrArg Subtype.val he)
    have ht' : (⟨t, htZ⟩ : center (Core z)) ≠ 1 := fun he => ht1 (congrArg Subtype.val he)
    exact congrArg Subtype.val ((hv _ hu').trans (hv _ ht').symm)
  obtain ⟨g, hgQ, hgz⟩ := h.fused
  obtain ⟨xH, hxQ, hxg⟩ := hgQ
  change (xH : G) = g * z * g⁻¹ at hxg
  let x : Core z := ⟨xH, hxQ⟩
  have hxconj : IsConj z (i x) := by
    change IsConj z (xH : G)
    rw [hxg]
    exact isConj_iff.mpr ⟨g, rfl⟩
  have hxZ : x ∉ center (Core z) := by
    intro hx
    rcases hcenter x hx with hx1 | hxt
    · exact hz1 (isConj_one_left.mp (by simpa only [hx1, map_one] using hxconj))
    · apply hgz
      exact hxg.symm.trans (congrArg i hxt)
  obtain ⟨f, hf3, hfix, hfconj⟩ := cubic_action h
  have hfnc (u : Core z) (hu : u ∉ center (Core z)) : f u ∉ center (Core z) := by
    intro hf
    exact hu ((hfix u).mp (f.injective ((hfix (f u)).mpr hf)))
  have hfxZ := hfnc x hxZ
  have hffxZ := hfnc (f x) hfxZ
  have hfxconj : IsConj z (i (f x)) := hxconj.trans (hfconj x)
  have hffxconj : IsConj z (i (f (f x))) := hfxconj.trans (hfconj (f x))
  let q := QuotientGroup.mk' (center (Core z))
  have hsq (v : Core z ⧸ center (Core z)) : v * v = 1 := by
    simpa only [pow_two] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Core z ⧸ center (Core z))) v)
  have hqx1 : q x ≠ 1 := fun he => hxZ ((QuotientGroup.eq_one_iff x).mp he)
  have hqfx1 : q (f x) ≠ 1 := fun he => hfxZ ((QuotientGroup.eq_one_iff (f x)).mp he)
  have hqne : q x ≠ q (f x) := fun he =>
    hxZ (cubic_quotient_fixed f hf3 hfix he.symm)
  have hnorm : q x * q (f x) * q (f (f x)) = 1 := by
    simpa only [map_mul] using cubic_norm f hf3 hfix x
  have hprod : q x * q (f x) = q (f (f x)) := by
    calc
      q x * q (f x) = (q x * q (f x) * q (f (f x))) * q (f (f x)) := by
        rw [mul_assoc, hsq, mul_one]
      _ = q (f (f x)) := by rw [hnorm, one_mul]
  let W := closure ({q x, q (f x)} : Set (Core z ⧸ center (Core z)))
  let : IsKleinFour W := isKleinFour_closure_pair _ _ (hsq _) (hsq _)
    hqx1 hqfx1 hqne (Commute.all _ _)
  have hW : Nat.card W = 4 := IsKleinFour.card_four
  let K := W.comap q
  have hK : Nat.card K = 8 := by
    have hquot := card_eq_card_quotient_mul_card_subgroup (center (Core z))
    rw [h.core_card, IsExtraspecial.center_order_p 2 (Core z)] at hquot
    have hindex := W.index_mul_card
    rw [hW] at hindex
    have hindex4 : W.index = 4 := by omega
    have hh := K.index_mul_card
    change (W.comap q).index * Nat.card K = Nat.card (Core z) at hh
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
      hindex4, h.core_card] at hh
    omega
  have hKfusion (u : Core z) (hu : u ∈ K) : i u = 1 ∨ IsConj z (i u) := by
    rcases (mem_closure_pair_iff (q x) (q (f x)) (hsq _) (hsq _)
      (Commute.all _ _) (q u)).mp hu with hu1 | hux | hufx | huffx
    · rcases hcenter u ((QuotientGroup.eq_one_iff u).mp hu1) with rfl | rfl
      · exact Or.inl (map_one i)
      · exact Or.inr (IsConj.refl z)
    · exact Or.inr (hxconj.trans (i.map_isConj
        (IsExtraspecial.isConj_of_center_quotient_eq hxZ hux.symm)))
    · exact Or.inr (hfxconj.trans (i.map_isConj
        (IsExtraspecial.isConj_of_center_quotient_eq hfxZ hufx.symm)))
    · exact Or.inr (hffxconj.trans (i.map_isConj
        (IsExtraspecial.isConj_of_center_quotient_eq hffxZ (huffx.trans hprod).symm)))
  let E := K.map i
  have hE : Nat.card E = 8 := (card_map_of_injective hi).trans hK
  let S : Set G := insert 1 {u : G | u ∈ coreInG z ∧ IsConj z u}
  have hone : (1 : G) ∉ {u : G | u ∈ coreInG z ∧ IsConj z u} :=
    fun hu => hz1 (isConj_one_left.mp hu.2)
  have hS : S.ncard = 8 := by
    change (insert (1 : G) {u : G | u ∈ coreInG z ∧ IsConj z u}).ncard = 8
    rw [Set.ncard_insert_of_notMem hone]
    change Nat.card {u : G // u ∈ coreInG z ∧ IsConj z u} + 1 = 8
    omega
  have hES : (E : Set G) ⊆ S := by
    rintro u ⟨v, hv, rfl⟩
    rcases hKfusion v hv with hv1 | hvf
    · exact Or.inl hv1
    · exact Or.inr ⟨mem_map_of_mem (Centralizer z).subtype v.property, hvf⟩
  have hset : (E : Set G) = S := Set.eq_of_subset_of_ncard_le hES (by
    change S.ncard ≤ Nat.card E
    rw [hS, hE])
  have hFE : fusionCore z ≤ E := by
    apply (closure_le _).mpr
    intro u hu
    rw [hset]
    exact Or.inr hu
  have hz2 : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  have hp (u : fusionCore z) : u ^ 2 = 1 := by
    apply Subtype.ext
    have hu : (u : G) ∈ S := hset ▸ hFE u.property
    rcases hu with hu1 | hu
    · simp only [hu1, one_pow, OneMemClass.coe_one, SubmonoidClass.coe_pow]
    · have hh := hu.2.pow 2
      rw [hz2] at hh
      exact isConj_one_right.mp hh
  have hinv (u : fusionCore z) : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp u)
  exact {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hinv _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hinv, hinv])
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
end CFSG.Quasithin.Extraspecial32.Hypotheses
