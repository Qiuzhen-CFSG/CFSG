module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.DoubleCoverConstruction
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Lifting projective fixed-Sylow saturation to the marked cover transvection

Let E = ⟨r,z⟩ and Z(L) = ⟨z⟩. In L, normalizing E is equivalent to being
fixed by r after projection to L/Z(L). Thus the projective fixed-Sylow
property lifts through the central two-kernel to Sylow saturation of
T ∩ L ∩ N_G(E) in L ∩ N_G(E), with the original T unchanged.

The intrinsic cover transvection has a component factor in Q ∩ L with
the same action on E. Conjugate that two-subgroup into the saturated
component normalizer. The conjugator fixes z, so its action on E commutes
with the transvection. This gives the requested actor inside T.

`ProjectiveFixedSylow` is an explicit, independent matrix-model obligation.
The source-level transfer constructs the marked central cover and its center
identity, but does not assert this remaining projective assertion. No position
of Q or Sylow maximality of N_T(E) is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1191. The projective obligation concerns the genuine
inverse-transpose/Frobenius automorphism of PSL₃(4).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection
open NormalizerModels
open Matrix.PSL3Four
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {r z g : G} {L R : Subgroup G}

/-- The intrinsic projective input: taking graph-field fixed points preserves
Sylow maximality for every invariant Sylow two-subgroup of PSL₃(4). -/
def ProjectiveFixedSylow : Prop :=
  ∀ S : Sylow 2 PSL,
    (S : Subgroup PSL).map graphField.toMonoidHom = (S : Subgroup PSL) →
    SylowIn ((S : Subgroup PSL) ⊓ graphField.fixedSubgroup) graphField.fixedSubgroup

private theorem comap_sylowIn {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {S H : Subgroup B} (h : SylowIn S H) :
    SylowIn (S.comap f) (H.comap f) := by
  obtain ⟨P, hP⟩ := h
  let N := H.comap f
  let q : N →* H := f.restrict (fun _ hx => hx)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, show f x ∈ H from hx ▸ y.property⟩, Subtype.ext hx⟩
  have hker : q.ker = f.ker.subgroupOf N := by
    ext x
    change q x = 1 ↔ f (x : A) = 1
    exact Subtype.ext_iff
  have hpker : IsPGroup 2 q.ker := by rw [hker]; exact hk.comap_subtype
  let U := P.comapOfKerIsPGroup q hpker (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  refine ⟨U, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hh : q y ∈ (P : Subgroup H) := hy
    exact hP ▸ mem_map_of_mem H.subtype hh
  · intro hx
    have hxH : f x ∈ H := by
      rw [← hP] at hx
      exact map_subtype_le _ hx
    let y : N := ⟨x, hxH⟩
    refine ⟨y, ?_, rfl⟩
    change q y ∈ (P : Subgroup H)
    rw [← hP] at hx
    obtain ⟨v, hv, he⟩ := hx
    have he' : v = q y := Subtype.ext he
    exact he' ▸ hv

private theorem sylow_component (h : IntersectionSetup T z L g R) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let H := normalizer (L : Set G)
  let J := L.subgroupOf H
  let : J.Normal := normal_in_normalizer
  obtain ⟨U, hU⟩ := (T.subtype h.sylow_normalizes).exists_subgroupOf_eq_of_normal J
  let e : J ≃* L := subgroupOfEquivOfLe L.le_normalizer
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hU] at hy
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [hU]
    exact hx

/-- The central quotient lifts the projective fixed-Sylow fact to the
component part of the marked normalizer, in the original T. -/
theorem component_normalizer_sylow (hfixed : ProjectiveFixedSylow)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (m : MarkedCover L r) :
    SylowIn ((T : Subgroup G) ⊓ (L ⊓ normalizer (fourGroup r z : Set G)))
      (L ⊓ normalizer (fourGroup r z : Set G)) := by
  let f := m.cover.toMonoidHom
  obtain ⟨S, hS⟩ := sylow_component h
  let B := S.mapSurjective (f := f) m.cover.surjective
  let a := L.normalizerMonoidHom ⟨r, m.actor_mem⟩
  have ha : (S : Subgroup L).map a.toMonoidHom = S := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      rw [hS] at hx ⊢
      change r * (x : G) * r⁻¹ ∈ (T : Subgroup G)
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem (h.le_sylow hr) hx)
        ((T : Subgroup G).inv_mem (h.le_sylow hr))
    · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
  have hb : (B : Subgroup PSL).map graphField.toMonoidHom = B := by
    change ((S : Subgroup L).map f).map graphField.toMonoidHom = _
    rw [map_map]
    have he : graphField.toMonoidHom.comp f = f.comp a.toMonoidHom := by
      ext x
      exact (m.compatible x).symm
    rw [he, ← map_map, ha]
    rfl
  have hkS : f.ker ≤ (S : Subgroup L) := m.kernel_two.le_sylow_of_normal S
  have hpre : (B : Subgroup PSL).comap f = (S : Subgroup L) :=
    comap_map_eq_self hkS
  have hh := comap_sylowIn f m.cover.surjective m.kernel_two (hfixed B hb)
  rw [comap_inf, hpre] at hh
  have hN := DoubleCoverConstruction.component_normalizer_eq_preimage h hr hr2 hout hZ m
  change (normalizer (fourGroup r z : Set G)).subgroupOf L =
    graphField.fixedSubgroup.comap f at hN
  rw [← hN, hS] at hh
  obtain ⟨P, hP⟩ := hh
  let N := L ⊓ normalizer (fourGroup r z : Set G)
  let e : ((normalizer (fourGroup r z : Set G)).subgroupOf L) ≃* N :=
    { toFun := fun x => ⟨x, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    have hv' := hP.le (mem_map_of_mem _ hv)
    exact ⟨hv'.1, v.val.property, v.property⟩
  · rintro ⟨hxT, hxL, hxN⟩
    have hm : (⟨x, hxL⟩ : L) ∈ (T : Subgroup G).subgroupOf L ⊓
        (normalizer (fourGroup r z : Set G)).subgroupOf L := ⟨hxT, hxN⟩
    obtain ⟨v, hv, he⟩ := hP.ge hm
    refine ⟨e v, ⟨v, hv, rfl⟩, ?_⟩
    exact congrArg Subtype.val he

private theorem four_nonidentity_cases
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4)
    (hr : r ≠ 1) (hz : z ≠ 1) (hrz : r ≠ z)
    {x : G} (hx : x ∈ fourGroup r z) (hx1 : x ≠ 1) :
    x = r ∨ x = z ∨ x = r * z := by
  let E := fourGroup r z
  let : IsElementaryAbelian 2 E := hE
  let : Nontrivial E := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; decide)
  let : IsKleinFour E := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  by_cases hxr : x = r
  · exact Or.inl hxr
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  right; right
  exact congrArg Subtype.val (IsKleinFour.eq_mul_of_ne_all
    (x := (⟨r, mem_sup_left (mem_zpowers r)⟩ : E))
    (y := (⟨z, mem_sup_right (mem_zpowers z)⟩ : E))
    (z := (⟨x, hx⟩ : E))
    (fun he => hr (congrArg Subtype.val he))
    (fun he => hz (congrArg Subtype.val he))
    (fun he => hrz (congrArg Subtype.val he))
    (fun he => hx1 (congrArg Subtype.val he))
    (fun he => hxr (congrArg Subtype.val he))
    (fun he => hxz (congrArg Subtype.val he)))



private theorem conjugated_transvection
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4)
    (hr : r ≠ 1) (hz : z ≠ 1) (hrz : r ≠ z)
    {a t : G} (ha : a ∈ normalizer (fourGroup r z : Set G))
    (haz : MulAut.conj a z = z) (htz : MulAut.conj t z = z)
    (htr : MulAut.conj t r = r * z) :
    MulAut.conj (a * t * a⁻¹) r = r * z := by
  have hai := (normalizer (fourGroup r z : Set G)).inv_mem ha
  have haiz : MulAut.conj a⁻¹ z = z := by
    have hh := congrArg (MulAut.conj a⁻¹) haz
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh.symm
  have h1 : MulAut.conj a⁻¹ r ≠ 1 :=
    fun he => hr ((MulAut.conj a⁻¹).map_eq_one_iff.mp he)
  have hnz : MulAut.conj a⁻¹ r ≠ z :=
    fun he => hrz ((MulAut.conj a⁻¹).injective (he.trans haiz.symm))
  apply (MulAut.conj a⁻¹).injective
  have he : MulAut.conj a⁻¹ (MulAut.conj (a * t * a⁻¹) r) =
      MulAut.conj t (MulAut.conj a⁻¹ r) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_mul, haiz]
  rcases four_nonidentity_cases hE hcard hr hz hrz
    ((mem_normalizer_iff.mp hai r).mp (mem_sup_left (mem_zpowers r))) h1 with
      hh | hh | hh
  · change MulAut.conj a⁻¹ r = r at hh
    rw [hh, htr]
  · exact (hnz hh).elim
  · change MulAut.conj a⁻¹ r = r * z at hh
    rw [hh, map_mul, htr, htz]

private theorem conjugate_into_sylow {S A H : Subgroup G} (hs : SylowIn S H)
    (ha : IsPGroup 2 A) (hle : A ≤ H) : ∃ a ∈ H, A.conjBy a ≤ S := by
  obtain ⟨U, hU⟩ := (ha.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  obtain ⟨a, ha, he⟩ := (show SylowIn ((U : Subgroup H).map H.subtype) H from
    ⟨U, rfl⟩).exists_conjugator hs
  refine ⟨a, ha, ?_⟩
  rw [← he]
  apply map_mono
  rw [← map_subgroupOf_eq_of_le hle]
  exact map_mono hU

/-- Once the intrinsic projective fixed-Sylow theorem is supplied, the model
transvection is realized in the fixed prepared T. The conjugation takes place
inside L ∩ N_G(E); it fixes z and preserves the transvection action on E. -/
theorem exists_transvection_of_projective_fixedSylow
    (hfixed : ProjectiveFixedSylow)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (m : MarkedCover L r)
    (d : NormalizerData L r z) (c : CoverActionData d) :
    ∃ t ∈ (T : Subgroup G) ⊓ normalizer (fourGroup r z : Set G),
      MulAut.conj t r = r * z := by
  have hE := fourGroup_elementary_card h hr hr2 hout
  let : IsElementaryAbelian 2 (fourGroup r z) := hE.1
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hrz : r ≠ z := by
    intro he
    exact hout (mem_sup_left (he ▸ central_involution_mem_centralizer h))
  obtain ⟨t, ht, htr⟩ := c.transvection
  have htprod : t ∈ ((L : Set G) * (fourGroup r z : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      ((fourGroup_le_sylow h hr).trans h.sylow_normalizes)]
    exact d.le_product ht
  obtain ⟨l, hl, e, he, hle⟩ := htprod
  have heQ : e ∈ d.Q := d.four_le he
  have hlQ : l ∈ d.Q := by
    have hh := d.Q.mul_mem ht (d.Q.inv_mem heQ)
    rwa [← hle, mul_inv_cancel_right] at hh
  have her : MulAut.conj e r = r := by
    have hc := (fourGroup r z).le_centralizer he r (mem_sup_left (mem_zpowers r))
    change e * r * e⁻¹ = r
    rw [← hc, mul_inv_cancel_right]
  have hlr : MulAut.conj l r = r * z := by
    have hh : MulAut.conj (l * e) r = MulAut.conj l (MulAut.conj e r) := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hle, hh, her] at htr
    exact htr
  have hsz := component_normalizer_sylow hfixed h hr hr2 hout hZ m
  obtain ⟨a, ha, hplace⟩ := conjugate_into_sylow hsz
    (d.two_group.to_inf_left (K := L)) (le_inf inf_le_right
      (inf_le_left.trans d.normalizes_four))
  have htnew := hplace (mem_map_of_mem (MulAut.conj a).toMonoidHom ⟨hlQ, hl⟩)
  refine ⟨a * l * a⁻¹, ⟨htnew.1, htnew.2.2⟩, ?_⟩
  have haz : MulAut.conj a z = z := by
    change a * z * a⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (h.component.1 ha.1), mul_inv_cancel_right]
  have hlz : MulAut.conj l z = z := by
    change l * z * l⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (h.component.1 hl), mul_inv_cancel_right]
  exact conjugated_transvection hE.1 hE.2 hr1 hz1 hrz ha.2 haz hlz hlr

/-- Source-level transfer with the marking and the center identity constructed
from the given graph-field action and the genuine center/two-core theorem.
The sole extra input is the independent projective fixed-Sylow assertion. -/
theorem exists_transvection_prepared_of_projective_fixedSylow {𝒦 : GroupClass}
    (hfixed : ProjectiveFixedSylow) (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (d : NormalizerData L r z) (c : CoverActionData d) :
    ∃ t ∈ (T : Subgroup G) ⊓ normalizer (fourGroup r z : Set G),
      MulAut.conj t r = r * z := by
  have hZ := center_eq_zpowers_of_nontrivial_core h hTC
    (hG.evenType.component_center_eq_twoCore h.involution h.component) hcore
  exact exists_transvection_of_projective_fixedSylow hfixed h hr hr2 hout hZ
    (markedCover hG h hmodel hD h9) d c

end CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection
