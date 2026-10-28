module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Actions
public import Theory.GroupAction.FourAutomorphismOrbit
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Frattini transfer of the four-group action

The Sylow conjugacy argument replaces any element of N_G(E) by one in
N_G(E) ∩ N_G(C_T(E)) with the same action on E. An action of order greater
than two contains a three-element; its two-residual is consequently
transitive on the three nonidentity elements of E. Both the normalizer and
the residual below are the actual ambient subgroups.

Source: Aschbacher–Smith, proof of 16.4.9(2), printed p.1191.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z r : G}

/-- Frattini lifts the action on E into the actual simultaneous normalizer. -/
theorem coverNormalizer_frattini
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    {x : G} (hx : x ∈ normalizer (fourGroup r z : Set G)) :
    ∃ a ∈ coverNormalizer T r z, ∀ e ∈ fourGroup r z,
      MulAut.conj a e = MulAut.conj x e := by
  let E := fourGroup r z
  let C := centralizer (E : Set G)
  let S := (T : Subgroup G) ⊓ C
  have hC : C.conjBy x = C :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer E hx)
  have hS : SylowIn (S.conjBy x) C := by
    have hh := hs.map (MulAut.conj x)
    change SylowIn (S.conjBy x) (C.conjBy x) at hh
    rwa [hC] at hh
  obtain ⟨c, hc, he⟩ := hS.exists_conjugator hs
  refine ⟨c * x, ⟨(normalizer (E : Set G)).mul_mem
    (centralizer_le_normalizer _ hc) hx, ?_⟩, ?_⟩
  · change c * x ∈ normalizer (S : Set G)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change S.conjBy (c * x) = S
    rw [conjBy_conjBy] at he
    exact he
  · intro e he
    have hxE : MulAut.conj x e ∈ E := (mem_normalizer_iff.mp hx e).mp he
    have hh := hc _ hxE
    change (c * x) * e * (c * x)⁻¹ = x * e * x⁻¹
    change (x * e * x⁻¹) * c = c * (x * e * x⁻¹) at hh
    calc
      _ = c * (x * e * x⁻¹) * c⁻¹ := by group
      _ = x * e * x⁻¹ := by rw [← hh, mul_inv_cancel_right]


/-- An action of order divisible by three remains transitive in its two-residual. -/
private theorem residual_action_transitive {A : Type*} [Group A] [Finite A]
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (f : A →* MulAut E) (hf : 2 < Nat.card f.range) :
    ∀ u : E, u ≠ 1 → ∀ v : E, v ≠ 1 →
      ∃ a ∈ pResidual 2 A, f a u = v := by
  let : Nontrivial E := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hE]; decide)
  let : IsKleinFour E := ⟨hE, IsElementaryAbelian.exponent_eq_prime⟩
  have hdiv : Nat.card f.range ∣ 6 :=
    (IsKleinFour.card_mulAut E) ▸ f.range.card_subgroup_dvd_card
  have hle : Nat.card f.range ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have h3 : 3 ∣ Nat.card f.range := by
    have hc : Nat.card f.range = 3 ∨ Nat.card f.range = 6 := by
      interval_cases hc : Nat.card f.range <;> simp_all
    rcases hc with hc | hc
    · rw [hc]
    · rw [hc]
      norm_num
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 3 h3
  have hbR : b ∈ pResidual 2 f.range :=
    mem_pResidual_of_orderOf_coprime (by rw [hb]; decide)
  have hmap := map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨a, ha, hab⟩ := hmap.symm.le hbR
  let K := (pResidual 2 A).map f
  have hbK : (b : MulAut E) ∈ K := ⟨a, ha, congrArg Subtype.val hab⟩
  have hcard : 2 < Nat.card K := by
    have hd := card_dvd_of_le (zpowers_le.mpr hbK)
    rw [Nat.card_zpowers, orderOf_coe b, hb] at hd
    exact lt_of_lt_of_le (by decide : 2 < 3) (Nat.le_of_dvd Nat.card_pos hd)
  intro u hu v hv
  obtain ⟨k, hku⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup hE K hcard u hu v hv)
  change (k : MulAut E) u = v at hku
  obtain ⟨a, ha, hak⟩ := k.property
  exact ⟨a, ha, by simpa only [hak] using hku⟩



/-- Paired transvections with distinct centers make the actual Y transitive. -/
theorem coverY_transitive_of_paired_transvections
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4) (hr : r ≠ 1) (hz : z ≠ 1)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    {t s : G} (htN : t ∈ normalizer (fourGroup r z : Set G))
    (hsN : s ∈ normalizer (fourGroup r z : Set G))
    (htr : MulAut.conj t r = r * z) (htz : MulAut.conj t z = z)
    (hsz : MulAut.conj s z = z * r) : CoverTransitive T r z := by
  classical
  let E := fourGroup r z
  let A := coverNormalizer T r z
  let f : A →* MulAut E := E.normalizerMonoidHom.comp (inclusion inf_le_left)
  let : IsElementaryAbelian 2 E := hE
  have hrE : r ∈ E := mem_sup_left (mem_zpowers r)
  have hzE : z ∈ E := mem_sup_right (mem_zpowers z)
  obtain ⟨a, ha, hat⟩ := coverNormalizer_frattini hs htN
  obtain ⟨b, hb, hbs⟩ := coverNormalizer_frattini hs hsN
  let ar : f.range := ⟨f ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
  let br : f.range := ⟨f ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have har : (ar : MulAut E) ⟨r, hrE⟩ = ⟨r * z, E.mul_mem hrE hzE⟩ :=
    Subtype.ext ((hat r hrE).trans htr)
  have haz : (ar : MulAut E) ⟨z, hzE⟩ = ⟨z, hzE⟩ :=
    Subtype.ext ((hat z hzE).trans htz)
  have hbz : (br : MulAut E) ⟨z, hzE⟩ = ⟨z * r, E.mul_mem hzE hrE⟩ :=
    Subtype.ext ((hbs z hzE).trans hsz)
  have ha1 : ar ≠ 1 := by
    intro hh
    have hh' := har
    rw [hh] at hh'
    have he : r * 1 = r * z := by simpa using congrArg Subtype.val hh'
    exact hz (mul_left_cancel he).symm
  have hb1 : br ≠ 1 := by
    intro hh
    have hh' := hbz
    rw [hh] at hh'
    have he : z * 1 = z * r := by simpa using congrArg Subtype.val hh'
    exact hr (mul_left_cancel he).symm
  have hab : ar ≠ br := by
    intro hh
    rw [hh] at haz
    have he : z * 1 = z * r := by simpa using congrArg Subtype.val (haz.symm.trans hbz)
    exact hr (mul_left_cancel he).symm
  have hlarge : 2 < Nat.card f.range := by
    let := Fintype.ofFinite f.range
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.mpr ⟨1, ar, br, ha1.symm, hb1.symm, hab⟩
  intro u hu hu1 v hv hv1
  obtain ⟨y, hy, hyv⟩ := residual_action_transitive hcard f hlarge
    ⟨u, hu⟩ (fun he => hu1 (congrArg Subtype.val he))
    ⟨v, hv⟩ (fun he => hv1 (congrArg Subtype.val he))
  exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyv⟩

/-- Normalizer models for L and its opposite act on the same marked E.
No assertion about a conjugator interchanging both generators is needed. -/
theorem coverY_transitive_of_models {L J : Subgroup G}
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4) (hr : r ≠ 1) (hz : z ≠ 1)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData J z r) (c' : CoverActionData d') :
    CoverTransitive T r z := by
  obtain ⟨t, ht, htr⟩ := c.transvection
  obtain ⟨s, hsQ, hsz⟩ := c'.transvection
  have hsN : s ∈ normalizer (fourGroup r z : Set G) := by
    simpa only [fourGroup, sup_comm] using d'.normalizes_four hsQ
  have htz : MulAut.conj t z = z := by
    change t * z * t⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (c.fixes_z ht), mul_inv_cancel_right]
  exact coverY_transitive_of_paired_transvections hE hcard hr hz hs
    (d.normalizes_four ht) hsN htr htz hsz

end CFSG.Quasithin.Chapter16.Intersections.GraphField
