module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport

/-!
# Inner section actions through an invariant overgroup

An ambient automorphism preserving A and H, with A ≤ H, restricts to H and
descends to H/O₂(H). Both operations preserve a two-power exponent. If the
descended automorphism is inner on the image section, lift its conjugator to
A. The displacement lies in O₂(A) by the core-preimage theorem for the actual
projection; neither normality of A in H nor a trivial image core is needed.

This is the transport step for the proposed Mathieu-overgroup route in J₄.
It does not assert the existence or invariance of such an overgroup.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 1.3.9,
printed p.514, with A.3.12(14),(17), pp.47–48.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer

variable {G : Type*} [Group G]

private def restriction (H : Subgroup G) (α : MulAut G)
    (hH : H.map α.toMonoidHom = H) : MulAut H :=
  (α.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

private theorem restriction_coe (H : Subgroup G) (α : MulAut G)
    (hH : H.map α.toMonoidHom = H) (x : H) :
    (restriction H α hH x : G) = α x := rfl

private theorem restriction_pow_coe (H : Subgroup G) (α : MulAut G)
    (hH : H.map α.toMonoidHom = H) (n : ℕ) (x : H) :
    ((restriction H α hH ^ n) x : G) = (α ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', MulAut.mul_apply, restriction_coe, ih]

private theorem restriction_two (H : Subgroup G) (α : MulAut G)
    (hH : H.map α.toMonoidHom = H) (hα : ∃ n : ℕ, α ^ (2 ^ n) = 1) :
    ∃ n : ℕ, restriction H α hH ^ (2 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hα
  refine ⟨n, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [restriction_pow_coe, hn]
  rfl

private theorem restriction_image {A H : Subgroup G} (hAH : A ≤ H)
    (α : MulAut G) (hH : H.map α.toMonoidHom = H)
    (hA : A.map α.toMonoidHom = A) :
    (twoQuotientImage A H).map
      (quotientAut (pCore 2 H) (restriction H α hH)).toMonoidHom =
        twoQuotientImage A H := by
  have hrestrict : (A.subgroupOf H).map (restriction H α hH).toMonoidHom =
      A.subgroupOf H := by
    apply (Subgroup.map_injective H.subtype_injective)
    have hc : H.subtype.comp (restriction H α hH).toMonoidHom =
        α.toMonoidHom.comp H.subtype := by ext x; rfl
    rw [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hAH, hA]
  let q := QuotientGroup.mk' (pCore 2 H)
  have hc : (quotientAut (pCore 2 H) (restriction H α hH)).toMonoidHom.comp q =
      q.comp (restriction H α hH).toMonoidHom := by
    ext x
    exact quotientAut_apply_mk _ _ x
  change ((A.subgroupOf H).map q).map _ = (A.subgroupOf H).map q
  rw [map_map, hc, ← map_map, hrestrict]

private theorem inner_of_restriction_image [Finite G] {A H : Subgroup G} (hAH : A ≤ H)
    (α : MulAut G) (hH : H.map α.toMonoidHom = H)
    (hA : A.map α.toMonoidHom = A)
    (hinner : IsInnerOnTwoQuotient (twoQuotientImage A H)
      (quotientAut (pCore 2 H) (restriction H α hH))) :
    IsInnerOnTwoQuotient A α := by
  obtain ⟨a, ha, hact⟩ := hinner
  obtain ⟨b, rfl⟩ := exists_preimage_twoQuotientImage hAH ha
  refine ⟨b, b.property, fun x hx => ?_⟩
  have hαx : α x ∈ A := hA ▸ mem_map_of_mem α.toMonoidHom hx
  have hz : (b : G)⁻¹ * α x * b * x⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem (A.inv_mem b.property) hαx) b.property) (A.inv_mem hx)
  have hc : (⟨(b : G)⁻¹ * α x * b * x⁻¹, hz⟩ : A) ∈ pCore 2 A := by
    apply mem_twoCore_of_projection_mem hAH
    have he := hact (twoQuotientImageMap hAH ⟨x, hx⟩)
      (mem_twoQuotientImage hAH ⟨x, hx⟩)
    let q := QuotientGroup.mk' (pCore 2 H)
    let xH : H := ⟨x, hAH hx⟩
    let bH : H := ⟨b, hAH b.property⟩
    have hzH : inclusion hAH (⟨(b : G)⁻¹ * α x * b * x⁻¹, hz⟩ : A) =
        bH⁻¹ * restriction H α hH xH * bH * xH⁻¹ := by
      apply Subtype.ext
      rfl
    change q (inclusion hAH _) ∈ _
    rw [hzH, map_mul, map_mul, map_mul, map_inv, map_inv]
    change (q bH)⁻¹ * quotientAut (pCore 2 H) (restriction H α hH) (q xH) *
      q bH * (q xH)⁻¹ ∈ _ at he
    rw [quotientAut_apply_mk] at he
    exact he
  exact mem_map_of_mem A.subtype hc

/-- Inner action in H/O₂(H) lifts to the original embedded section of A.
The overgroup must be preserved by this particular ambient automorphism. -/
theorem isInnerOnTwoQuotient_of_invariant_overgroup [Finite G]
    {A H : Subgroup G} (hAH : A ≤ H) (α : MulAut G)
    (htwo : ∃ n : ℕ, α ^ (2 ^ n) = 1)
    (hA : A.map α.toMonoidHom = A) (hH : H.map α.toMonoidHom = H)
    (hinner : TwoStabilizerActsInner (twoQuotientImage A H)) :
    IsInnerOnTwoQuotient A α := by
  apply inner_of_restriction_image hAH α hH hA
  apply hinner _ ?_ (restriction_image hAH α hH hA)
  obtain ⟨n, hn⟩ := restriction_two H α hH htwo
  refine ⟨n, ?_⟩
  rw [← map_pow, hn, map_one]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
