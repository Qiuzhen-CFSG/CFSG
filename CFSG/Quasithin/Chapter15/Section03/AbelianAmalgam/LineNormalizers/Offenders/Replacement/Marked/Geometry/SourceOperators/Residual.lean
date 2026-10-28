module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.SourceOperators.Seed

/-!
# Cubic residual actions and the marked inversion relation

Restriction to the actual four-group E detects the residual action on U.
The action on E is its faithful three-point permutation action: every
residual element has cube one, and a nonidentity original quotient image
generates its three possible actions. The selected τ is a nonidentity
involution there and inverts the residual action. The propagated residual
kernel lifts these statements to the full module U.

For the cubic polynomial, the norm 1+t+t² annihilates every residual
commutator. The original equality U=[U,Y_E] makes it vanish on all of U.
No quotient-module decomposition or fixed-representative premise is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
variable {G D : Type*} [Group G] [Group D] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

omit [IsMulCommutative V] in
/-- Every residual cube centralizes the full span. -/
theorem residual_cube_centralizes_span (d : OriginalData Y T V M E Pc)
    (y : G) (hy : y ∈ lineY Y E) : y ^ 3 ∈ centralizer (lineV V E : Set G) := by
  apply d.residual_core_centralizes_span
  rw [Orthogonal.lineY_twoCore d.action Y E d.Y_le d.line_le
    d.residual_image d.residual_kernel]
  exact ⟨(lineY Y E).pow_mem hy 3, Orthogonal.lineY_cube_centralizes_module
    d.action Y E d.Y_le d.line_le d.residual_image y hy⟩

omit [IsMulCommutative V] in
/-- A nonidentity original residual quotient element acts nontrivially on E. -/
theorem residual_line_action_ne_one (d : OriginalData Y T V M E Pc)
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) :
    E.normalizerMonoidHom ⟨y, (lineY_le Y E hy).2⟩ ≠ 1 := by
  intro he
  have hcentral : y ∈ centralizer (E : Set G) := by
    intro e heE
    have h := congrArg (fun a : MulAut E => (a ⟨e, heE⟩ : G)) he
    change y * e * y⁻¹ = e at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hk : y ∈ twoCoreAmbient (lineY Y E) := by
    rw [Orthogonal.lineY_twoCore d.action Y E d.Y_le d.line_le
      d.residual_image d.residual_kernel]
    exact (Orthogonal.lineY_centralizer_line_eq_module d.action Y E d.Y_le
      d.line_le d.line_card d.singular d.residual_image).le ⟨hy, hcentral⟩
  have hQ : y ∈ lineQ E := by
    have heq := Descent.QuotientIdentification.lineY_twoCore Y E
      ((normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mpr
        d.residual_normal)
    exact (heq.le hk).2
  obtain ⟨x, hx, hxy⟩ := hQ
  apply hne
  have hxe : x = (⟨y, (lineY_le Y E hy).2⟩ : lineNormalizer E) := Subtype.ext hxy
  subst x
  exact (QuotientGroup.eq_one_iff _).mpr hx

/-- Agreement on E determines the residual image in every faithful U-action. -/
theorem residual_images_eq_of_line_action_eq (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (x z : G) (hx : x ∈ lineY Y E) (hz : z ∈ lineY Y E)
    (he : E.normalizerMonoidHom ⟨x, (lineY_le Y E hx).2⟩ =
      E.normalizerMonoidHom ⟨z, (lineY_le Y E hz).2⟩) :
    f (d.residualElement x hx) = f (d.residualElement z hz) := by
  have hn : x * z⁻¹ ∈ lineY Y E := (lineY Y E).mul_mem hx ((lineY Y E).inv_mem hz)
  have ha : E.normalizerMonoidHom ⟨x * z⁻¹, (lineY_le Y E hn).2⟩ = 1 := by
    change E.normalizerMonoidHom
      ((⟨x, (lineY_le Y E hx).2⟩ : lineNormalizer E) * ⟨z, (lineY_le Y E hz).2⟩⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hc : x * z⁻¹ ∈ centralizer (E : Set G) := by
    intro e heE
    have hh := congrArg (fun a : MulAut E => (a ⟨e, heE⟩ : G)) ha
    change (x * z⁻¹) * e * (x * z⁻¹)⁻¹ = e at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hU := ((d.residual_centralizer_line_eq_span).le ⟨hn, hc⟩).2
  have hk : d.residualElement x hx * (d.residualElement z hz)⁻¹ ∈ f.ker := by
    rw [hker]
    intro u hu
    exact Subtype.ext (hU (u : G) hu)
  have hh := MonoidHom.mem_ker.mp hk
  rw [map_mul, map_inv, mul_inv_eq_one] at hh
  exact hh

private theorem perm_three_cubic_cases : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 → b = 1 ∨ b = a ∨ b = a ^ 2 := by
  decide +kernel

private theorem perm_three_inverts : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 3 = 1 → b ^ 2 = 1 → b ≠ 1 → b * a⁻¹ * b⁻¹ = a := by
  decide +kernel

omit [IsMulCommutative V] in
private theorem residual_line_action_cube (d : OriginalData Y T V M E Pc)
    (y : G) (hy : y ∈ lineY Y E) :
    (E.normalizerMonoidHom ⟨y, (lineY_le Y E hy).2⟩) ^ 3 = 1 := by
  rw [← map_pow, ← MonoidHom.mem_ker, E.normalizerMonoidHom_ker]
  exact centralizer_le d.line_le (Orthogonal.lineY_cube_centralizes_module
    d.action Y E d.Y_le d.line_le d.residual_image y hy)

/-- The nonidentity original residual image generates all residual actions on U. -/
theorem residual_image_cases (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) (z : G) (hz : z ∈ lineY Y E) :
    f (d.residualElement z hz) = 1 ∨
      f (d.residualElement z hz) = f (d.residualElement y hy) ∨
      f (d.residualElement z hz) = f (d.residualElement y hy) ^ 2 := by
  let := Orthogonal.singularLine_isKleinFour d.action E d.line_le d.line_card d.singular
  let e := IsKleinFour.autEquivPermThree E
  let ay := E.normalizerMonoidHom ⟨y, (lineY_le Y E hy).2⟩
  let az := E.normalizerMonoidHom ⟨z, (lineY_le Y E hz).2⟩
  have hy3 : e ay ^ 3 = 1 := by rw [← map_pow, d.residual_line_action_cube y hy, map_one]
  have hz3 : e az ^ 3 = 1 := by rw [← map_pow, d.residual_line_action_cube z hz, map_one]
  have hyn : e ay ≠ 1 := by
    intro h
    exact d.residual_line_action_ne_one y hy hne
      (e.injective (h.trans (map_one e).symm))
  rcases perm_three_cubic_cases (e ay) (e az) hy3 hyn hz3 with h | h | h
  · left
    have hh : az = 1 := e.injective (h.trans (map_one e).symm)
    have hr := d.residual_images_eq_of_line_action_eq f hker z 1 hz (one_mem _)
      (hh.trans (map_one E.normalizerMonoidHom).symm)
    exact hr.trans (map_one f)
  · right; left
    exact d.residual_images_eq_of_line_action_eq f hker z y hz hy (e.injective h)
  · right; right
    have hh : az = ay ^ 2 := e.injective (h.trans (map_pow e ay 2).symm)
    have hp : E.normalizerMonoidHom ⟨y ^ 2, (lineY_le Y E ((lineY Y E).pow_mem hy 2)).2⟩ =
        ay ^ 2 := map_pow E.normalizerMonoidHom ⟨y, (lineY_le Y E hy).2⟩ 2
    have hr := d.residual_images_eq_of_line_action_eq f hker z (y ^ 2) hz
      ((lineY Y E).pow_mem hy 2) (hh.trans hp.symm)
    exact hr.trans (map_pow f (d.residualElement y hy) 2)

/-- The original marked τ inverts the residual action on U. -/
theorem residual_image_inverted (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E) :
    f d.tau * (f (d.residualElement y hy))⁻¹ * (f d.tau)⁻¹ =
      f (d.residualElement y hy) := by
  let := Orthogonal.singularLine_isKleinFour d.action E d.line_le d.line_card d.singular
  let e := IsKleinFour.autEquivPermThree E
  let ay := E.normalizerMonoidHom ⟨y, (lineY_le Y E hy).2⟩
  let aτ := E.normalizerMonoidHom ⟨d.marked.tau, d.marked.tau_mem.2⟩
  have hy3 : e ay ^ 3 = 1 := by rw [← map_pow, d.residual_line_action_cube y hy, map_one]
  have ht2 : aτ ^ 2 = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, E.normalizerMonoidHom_ker]
    exact centralizer_le d.line_le
      (d.sylow_square_centralizes_seed d.marked.tau d.marked.tau_mem)
  have htn : aτ ≠ 1 := by
    intro hh
    have hc : (⟨d.marked.tau, d.marked.tau_mem.2⟩ : lineNormalizer E) ∈
        E.normalizerMonoidHom.ker := hh
    rw [E.normalizerMonoidHom_ker] at hc
    exact d.tau_outside ⟨d.marked.tau_mem.1, hc⟩
  have hte : e aτ ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have htne : e aτ ≠ 1 := by
    intro h
    exact htn (e.injective (h.trans (map_one e).symm))
  have hi : aτ * ay⁻¹ * aτ⁻¹ = ay := by
    apply e.injective
    simpa only [map_mul, map_inv] using perm_three_inverts (e ay) (e aτ) hy3 hte htne
  have hconj : d.marked.tau * y⁻¹ * d.marked.tau⁻¹ ∈ lineY Y E :=
    (d.residual_normal d.marked.tau_mem.2 y⁻¹).mp ((lineY Y E).inv_mem hy)
  have he : E.normalizerMonoidHom
      ⟨d.marked.tau * y⁻¹ * d.marked.tau⁻¹, (lineY_le Y E hconj).2⟩ = ay := by
    change E.normalizerMonoidHom
      ((⟨d.marked.tau, d.marked.tau_mem.2⟩ : lineNormalizer E) *
        ⟨y, (lineY_le Y E hy).2⟩⁻¹ * ⟨d.marked.tau, d.marked.tau_mem.2⟩⁻¹) = ay
    simpa only [map_mul, map_inv] using hi
  have hr := d.residual_images_eq_of_line_action_eq f hker _ y hconj hy he
  change f (d.tau * (d.residualElement y hy)⁻¹ * d.tau⁻¹) = _ at hr
  simpa only [map_mul, map_inv] using hr

open Representation.NormalElementaryQuotient
/-- Residual cubes act trivially in the faithful intrinsic image. -/
theorem residual_image_cube (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E) : f (d.residualElement y hy) ^ 3 = 1 := by
  rw [← map_pow, ← MonoidHom.mem_ker, hker]
  intro u hu
  exact Subtype.ext (d.residual_cube_centralizes_span y hy (u : G) hu)

/-- The inversion identity in the full original binary module. -/
theorem operator_inverts (d : OriginalData Y T V M E Pc)
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E) :
    representation _ f hf hker (f d.tau) *
      representation _ f hf hker (f (d.residualElement y hy)⁻¹) =
    representation _ f hf hker (f (d.residualElement y hy)⁻¹) ^ 2 *
      representation _ f hf hker (f d.tau) := by
  let ρ := representation _ f hf hker
  have h3 := d.residual_image_cube f hker y hy
  have hi := d.residual_image_inverted f hker y hy
  have hp : (f (d.residualElement y hy))⁻¹ ^ 2 = f (d.residualElement y hy) := by
    have hc : f (d.residualElement y hy) ^ 2 * f (d.residualElement y hy) = 1 := by
      simpa only [← pow_succ] using h3
    rw [inv_pow, eq_inv_of_mul_eq_one_left hc, inv_inv]
  rw [map_inv, ← map_pow, hp, ← map_mul, ← map_mul]
  exact congrArg ρ (mul_inv_eq_iff_eq_mul.mp hi)

/-- The norm of the chosen nonidentity residual element kills U=[U,Y_E]. -/
theorem operator_cubic (d : OriginalData Y T V M E Pc)
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) :
    representation _ f hf hker (f (d.residualElement y hy)⁻¹) ^ 2 +
      representation _ f hf hker (f (d.residualElement y hy)⁻¹) + 1 = 0 := by
  let H := temporaryLineNormalizer T V E
  let U := (lineV V E).subgroupOf H
  let R := (lineY Y E).subgroupOf H
  let ρ := representation U f hf hker
  let t := ρ (f (d.residualElement y hy)⁻¹)
  let N := t ^ 2 + t + 1
  have ht3 : t ^ 3 = 1 := by
    change ρ (f (d.residualElement y hy)⁻¹) ^ 3 = 1
    rw [← map_pow, map_inv, inv_pow, d.residual_image_cube f hker y hy, inv_one, map_one]
  have hNt : N * t = N := by
    dsimp [N]
    rw [add_mul, add_mul, one_mul, ← pow_succ, ← pow_two, ht3]
    abel
  have hNtt : N * t ^ 2 = N := by rw [pow_two, ← mul_assoc, hNt, hNt]
  have hyi := (lineY Y E).inv_mem hy
  have hnei : Descent.QuotientIdentification.quotientMap E
      ⟨y⁻¹, (lineY_le Y E hyi).2⟩ ≠ 1 := by
    change Descent.QuotientIdentification.quotientMap E
      ((⟨y, (lineY_le Y E hy).2⟩ : lineNormalizer E)⁻¹) ≠ 1
    rwa [map_inv, inv_ne_one]
  have hNR (r : H) (hr : r ∈ R) : N * ρ (f r) = N := by
    rcases d.residual_image_cases f hker y⁻¹ hyi hnei r hr with h | h | h
    · change f r = 1 at h
      rw [h, map_one, mul_one]
    · change f r = f (d.residualElement y hy)⁻¹ at h
      rw [h]; exact hNt
    · change f r = f (d.residualElement y hy)⁻¹ ^ 2 at h
      rw [h, map_pow]; exact hNtt
  have hmove : U = ⁅U, R⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le d.span_le_temporary,
      map_subgroupOf_eq_of_le d.inherited.2.1]
    exact d.residual_span
  let n : U →* Multiplicative (Additive U) := {
    toFun u := Multiplicative.ofAdd (N (Additive.ofMul u))
    map_one' := map_zero N
    map_mul' u v := map_add N (Additive.ofMul u) (Additive.ofMul v) }
  have hkill : ⁅U, R⁆ ≤ n.ker.map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr u hu
    let w : Additive U := Additive.ofMul ⟨u, hu⟩
    refine ⟨(ρ (f r) w - w).toMul, ?_, ?_⟩
    · change N (ρ (f r) w - w) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun (hNR r hr) w)
    · change ((ρ (f r) w).toMul : H) / (w.toMul : H) = ⁅r, u⁆
      rw [representation_apply, div_eq_mul_inv]
      rfl
  apply LinearMap.ext
  intro w
  have hw := hkill (hmove.le w.toMul.property)
  obtain ⟨v, hv, he⟩ := hw
  have hve : v = w.toMul := Subtype.ext he
  subst v
  exact hv

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
