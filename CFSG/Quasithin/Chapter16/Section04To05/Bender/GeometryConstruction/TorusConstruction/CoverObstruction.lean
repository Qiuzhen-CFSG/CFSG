module
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Assembly

/-!
# The covered Suzuki obstruction to the published action interface

Equality of the actual normalizer images forces every element of T_L to
induce an automorphism of U_L whose order divides both a power of two and
2^n−1. Thus T_L centralizes U_L. If Z(T_L)=Z(L), as in the nonsimple
Suzuki cover of I.2.2(4), this places U_L in C_G(L), making [V,X] trivial.
This contradicts the required moved-subgroup order 2^n.

This is an obstruction to constructing `LocalAction` in the covered case
from intrinsic model facts alone. It is not a counterexample to Proposition
16.5.1 under its full ambient hypotheses: those may exclude the covered
configuration. Such an exclusion, or another source-supported repair of the
assembly route, remains a separate obligation. The existing `LocalAction`
interface and all source hypotheses are preserved.

Source: Aschbacher–Smith, I.2.2(4), printed p.409, and the first and third
paragraphs of Proposition 16.5.1, printed p.1194, manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- Equality of the two actual action images implies pointwise torus coverage
on the component omega subgroup. -/
theorem omegaNormalizerAction_of_localAction {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : LocalAction T L R n) : OmegaNormalizerAction T L d.actor := by
  intro l hl hlU
  have hLC : L ≤ centralizer (omegaOneAmbient (commutingSylow T L) : Set G) :=
    le_centralizer_iff.mp ((omegaOneAmbient_le _).trans inf_le_right)
  have hlV : l ∈ normalizer (benderSpace T L : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨centralizer_le_normalizer _ (hLC hl), hlU⟩
  let lN : normalizer (benderSpace T L : Set G) := ⟨l, hlV⟩
  have hm : (benderSpace T L).normalizerMonoidHom.rangeRestrict lN ∈
      inducedActor (benderSpace T L) d.actor := by
    rw [d.image_eq]
    exact ⟨lN, hl, rfl⟩
  obtain ⟨xN, hx, he⟩ := hm
  refine ⟨⟨xN, hx⟩, ?_⟩
  intro u hu
  let v : benderSpace T L := ⟨u, (show omegaOneAmbient (componentSylow T L) ≤ benderSpace T L from le_sup_right) hu⟩
  have hev := congrArg (fun a : ActionImage (benderSpace T L) =>
    (a : MulAut (benderSpace T L)) v) he
  exact congrArg Subtype.val hev

variable [Finite G]

/-- An odd torus cannot cover a nontrivial two-group action on U_L. -/
theorem omegaNormalizerAction_centralizes_sylow
    {T : Sylow 2 G} {L X : Subgroup G} {n : ℕ}
    (hX : X ≤ L ⊓ normalizer (componentSylow T L : Set G))
    (hcard : Nat.card X = 2 ^ n - 1) (hn : 2 ≤ n)
    (hnorm : OmegaNormalizerAction T L X) :
    omegaOneAmbient (componentSylow T L) ≤ centralizer (componentSylow T L : Set G) := by
  let P := componentSylow T L
  let U := omegaOneAmbient P
  have hPU : P ≤ normalizer (U : Set G) :=
    P.le_normalizer.trans (normalizer_le_omega_normalizer P)
  have hXU : X ≤ normalizer (U : Set G) :=
    (hX.trans inf_le_right).trans (normalizer_le_omega_normalizer P)
  let f : P →* MulAut U := U.normalizerMonoidHom.comp (inclusion hPU)
  let j : X →* MulAut U := U.normalizerMonoidHom.comp (inclusion hXU)
  have hP : IsPGroup 2 P := T.isPGroup'.of_injective
    (inclusion (show P ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime (2 ^ k) (2 ^ n - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    exact (Nat.odd_sub' (Nat.one_le_pow n 2 (by decide))).mpr (by simpa using he)
  intro u hu a ha
  let aP : P := ⟨a, ha⟩
  obtain ⟨x, hx⟩ := hnorm a ha.2 (hPU ha)
  have he : j x = f aP := by
    apply MulEquiv.ext
    intro v
    exact Subtype.ext (hx v v.property)
  have ht : orderOf (f aP) ∣ 2 ^ k :=
    hk ▸ (orderOf_map_dvd f aP).trans (orderOf_dvd_natCard aP)
  have ho : orderOf (f aP) ∣ 2 ^ n - 1 := by
    rw [← he, ← hcard]
    exact (orderOf_map_dvd j x).trans (orderOf_dvd_natCard x)
  have ho1 : orderOf (f aP) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd ht ho)
  have hv := congrArg (fun b : MulAut U => b ⟨u, hu⟩) (orderOf_eq_one_iff.mp ho1)
  have hv' : a * u * a⁻¹ = u := congrArg Subtype.val hv
  exact mul_inv_eq_iff_eq_mul.mp hv'

/-- The published LocalAction cannot hold in a cover whose Sylow center is
exactly the component center. This is the literal I.2.2(4) Suzuki-cover clause. -/
theorem no_localAction_of_sylow_center
    {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hcenter : (center (componentSylow T L)).map (componentSylow T L).subtype =
      (center L).map L.subtype) : ¬ Nonempty (LocalAction T L R n) := by
  rintro ⟨d⟩
  have hUC := omegaNormalizerAction_centralizes_sylow d.actor_le d.actor_card hn
    (omegaNormalizerAction_of_localAction d)
  have hUK : omegaOneAmbient (componentSylow T L) ≤ centralizer (L : Set G) := by
    intro u hu
    have huZ : u ∈ (center (componentSylow T L)).map (componentSylow T L).subtype := by
      refine ⟨⟨u, omegaOneAmbient_le _ hu⟩, ?_, rfl⟩
      exact mem_center_iff.mpr fun a => Subtype.ext (hUC hu a a.property)
    rw [hcenter] at huZ
    obtain ⟨uL, huL, rfl⟩ := huZ
    intro a ha
    exact congrArg L.subtype (mem_center_iff.mp huL ⟨a, ha⟩)
  have hVK : benderSpace T L ≤ centralizer (L : Set G) :=
    sup_le ((omegaOneAmbient_le _).trans inf_le_right) hUK
  have hz : ⁅benderSpace T L, d.actor⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hVK.trans (centralizer_le (d.actor_le.trans inf_le_left)))
  have hc := d.moved_card
  rw [hz, card_bot] at hc
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  omega

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
