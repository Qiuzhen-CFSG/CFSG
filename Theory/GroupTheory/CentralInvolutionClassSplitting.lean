module
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Splitting off a central involution from a generating involution class

A perfect normal subgroup covering the derived subgroup modulo a central
kernel is the full derived subgroup whenever the quotient has a cyclic
supplement: lift the supplement and adjoin the central kernel to obtain an
abelian supplement upstairs.

A single generating involution class then makes the abelianization have order
at most two. Any disjoint subgroup of order two embeds in it and supplies the
whole complement; the generating class lies in its nonidentity coset.
These general group-theoretic facts are used by the ZD simple-cover branch.

Source: GLS4, Chapter 2, Lemma 4.5, final paragraph, printed p. 35.
-/

namespace Theory.GroupTheory.CentralInvolutionClass

private theorem commutative_sup_central {G : Type*} [Group G]
    (A : Subgroup G) (hAc : A ≤ Subgroup.center G) (t : G) :
    IsMulCommutative (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact hAc.trans (Subgroup.center_le_centralizer _)
  · apply Subgroup.le_centralizer_iff.mpr
    exact sup_le (hAc.trans (Subgroup.center_le_centralizer _))
      (Subgroup.zpowers t).le_centralizer

/-- An abelian supplement in the central extension identifies its derived subgroup. -/
public theorem derived_eq_component {G : Type*} [Group G] [Finite G]
    (A K : Subgroup G) [A.Normal] [K.Normal]
    (hAc : A ≤ Subgroup.center G) [Group.IsPerfect K]
    (hmap : K.map (QuotientGroup.mk' A) = commutator (G ⧸ A))
    (u : G ⧸ A) (hu : commutator (G ⧸ A) ⊔ Subgroup.zpowers u = ⊤) :
    commutator G = K := by
  let q := QuotientGroup.mk' A
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective A u
  have hsup : K ⊔ (A ⊔ Subgroup.zpowers t) = ⊤ := by
    apply Subgroup.map_injective_of_ker_le q
      (by rw [QuotientGroup.ker_mk']; exact le_sup_of_le_right le_sup_left) le_top
    have hA : A.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.map_sup, Subgroup.map_sup, hmap, hA, bot_sup_eq, MonoidHom.map_zpowers,
      ht, hu, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective A)]
  apply le_antisymm
  · exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (commutative_sup_central A hAc t)
  · rw [← Subgroup.commutator_eq_self (H := K)]
    exact Subgroup.commutator_mono le_top le_top

/-- The central subgroup of order two is the entire complement to the derived
subgroup when one involution class generates. The last clause places that
class in its nonidentity coset. -/
public theorem split_of_one_class {G : Type*} [Group G] [Finite G]
    {Z : Set G} (hgen : Subgroup.closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (hsq : ∀ z ∈ Z, z ^ 2 = 1) (hne : Z.Nonempty)
    (A K : Subgroup G) [A.Normal] [K.Normal]
    (hAcard : Nat.card A = 2) (hdis : Disjoint K A)
    (hder : commutator G = K) :
    K ⊔ A = ⊤ ∧ ∃ u : G, u ∈ A ∧ u ≠ 1 ∧ u ^ 2 = 1 ∧
      Subgroup.zpowers u = A ∧ ∀ z ∈ Z, u⁻¹ * z ∈ K := by
  classical
  let r := QuotientGroup.mk' K
  let : IsMulCommutative (G ⧸ K) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder.le
  have hsame {x z : G} (hx : x ∈ Z) (hz : z ∈ Z) : r x = r z := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (hclass x hx z hz)
    have hh := congrArg r hg
    change r (g * x * g⁻¹) = r z at hh
    simpa only [map_mul, map_inv, mul_comm' (r g) (r x), mul_inv_cancel_right] using hh
  obtain ⟨z, hz⟩ := hne
  have hzp : Subgroup.zpowers (r z) = ⊤ := by
    apply top_unique
    rw [← Subgroup.map_top_of_surjective r (QuotientGroup.mk'_surjective K), ← hgen,
      MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨w, hw, rfl⟩
    rw [hsame hw hz]
    exact Subgroup.mem_zpowers _
  have hcardQ : Nat.card (G ⧸ K) ≤ 2 := by
    rw [← orderOf_eq_card_of_zpowers_eq_top hzp]
    apply Nat.le_of_dvd (by decide : 0 < 2)
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hsq z hz, map_one]
  have hAinj : Function.Injective (r.comp A.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis
      ((QuotientGroup.eq_one_iff (a : G)).mp ha) a.property
  have hArange : (r.comp A.subtype).range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Nat.card_congr (Subgroup.topEquiv.toEquiv),
      ← Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv, hAcard]
    exact hcardQ
  have hsup : K ⊔ A = ⊤ := by
    apply Subgroup.map_injective_of_ker_le r
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left) le_top
    have hAr : A.map r = ⊤ := by
      simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using hArange
    rw [Subgroup.map_sup, hAr, sup_top_eq,
      Subgroup.map_top_of_surjective r (QuotientGroup.mk'_surjective K)]
  obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
  have huG : (u : G) ≠ 1 := fun hh => hu (Subtype.ext hh)
  have hu2 : (u : G) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := u)
    rw [hAcard] at hh
    exact congrArg Subtype.val hh
  have huA : Subgroup.zpowers (u : G) = A := by
    apply le_antisymm (Subgroup.zpowers_le.mpr u.property)
    intro a ha
    by_cases ha1 : (⟨a, ha⟩ : A) = 1
    · have : a = 1 := congrArg Subtype.val ha1
      rw [this]; exact Subgroup.one_mem _
    · have : a = (u : G) := congrArg Subtype.val (huniq ⟨a, ha⟩ ha1)
      rw [this]; exact Subgroup.mem_zpowers _
  refine ⟨hsup, u, u.property, huG, hu2, huA, ?_⟩
  have hznot {w : G} (hw : w ∈ Z) : w ∉ K := by
    intro hwK
    have hZK : Subgroup.closure Z ≤ K := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      exact (hsame hx hw).trans ((QuotientGroup.eq_one_iff w).mpr hwK)
    have huK : (u : G) ∈ K := hZK (hgen ▸ Subgroup.mem_top _)
    exact huG (Subgroup.disjoint_def.mp hdis huK u.property)
  intro w hw
  obtain ⟨a, ha⟩ := (MonoidHom.range_eq_top.mp hArange) (r w)
  have ha1 : a ≠ 1 := by
    intro hh
    apply hznot hw
    apply (QuotientGroup.eq_one_iff w).mp
    change r w = 1
    simpa only [hh, map_one] using ha.symm
  have hau : a = u := huniq a ha1
  apply (QuotientGroup.eq_one_iff _).mp
  change r ((u : G)⁻¹ * w) = 1
  rw [map_mul, map_inv, ← ha]
  change (r (u : G))⁻¹ * r (a : G) = 1
  rw [hau, inv_mul_cancel]

end Theory.GroupTheory.CentralInvolutionClass
