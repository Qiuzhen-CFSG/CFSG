module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer
public import Theory.GroupTheory.PRegularLift


/-!
# Lifting the order-three generators through the star quotient

A homomorphism with two-group kernel carries θ(X) onto θ(Xᶠ). To lift an
order-three element, first choose an odd-order preimage; its cube lies in
the two-group kernel and therefore is trivial. Applied to H → H/O₂(H),
this identifies the star image of θ(L) with θ(L*).

Consequently an escaping order-three subgroup of L* supplies the literal
premise θ(L) ≰ Y₀ required by ResidualNormalizer. Relative containment
L ≤ H is retained; no ambient normality is imposed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
variable {G D : Type*} [Group G] [Group D]

private theorem order_three_lift [Finite G] (f : G →* D)
    (hk : IsPGroup 2 f.ker) (y : D) (hy : y ∈ f.range) (hy3 : orderOf y = 3) :
    ∃ x : G, f x = y ∧ orderOf x = 3 := by
  let y' : f.range := ⟨y, hy⟩
  have hy' : orderOf y' = 3 := (Subgroup.orderOf_coe y').symm.trans hy3
  obtain ⟨x, hodd, he⟩ := f.rangeRestrict.exists_pRegular_lift
    f.rangeRestrict_surjective 2 Nat.prime_two y' (by rw [hy']; decide)
  have hfx : f x = y := congrArg Subtype.val he
  have hc : x ^ 3 ∈ f.ker := by
    change f (x ^ 3) = 1
    rw [map_pow, hfx, ← hy3]
    exact pow_orderOf_eq_one y
  let z : f.ker := ⟨x ^ 3, hc⟩
  have hd : orderOf z ∣ orderOf x := by
    rw [← Subgroup.orderOf_coe z]
    exact orderOf_pow_dvd 3
  have hcop := hk.orderOf_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr hodd) z
  have hz : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
  have hx3 : x ^ 3 = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hz)
  have hxne : x ≠ 1 := by
    intro h
    have hyone : y = 1 := hfx.symm.trans (h ▸ f.map_one)
    simp [hyone] at hy3
  exact ⟨x, hfx, orderOf_eq_prime hx3 hxne⟩

theorem theta_map_of_twoGroup_ker [Finite G] (f : G →* D)
    (hk : IsPGroup 2 f.ker) (X : Subgroup G) :
    (theta X).map f = theta (X.map f) := by
  apply le_antisymm
  · rw [theta, MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
    have hd : orderOf (f x) ∣ 3 := hx3 ▸ orderOf_map_dvd f x
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    · exact subset_closure ⟨mem_map_of_mem f hx, h3⟩
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨⟨x, hx, hxy⟩, hy3⟩
    let fX := f.comp X.subtype
    have hkX : IsPGroup 2 fX.ker := hk.comap_of_injective X.subtype X.subtype_injective
    obtain ⟨u, hu, hu3⟩ := order_three_lift fX hkX y ⟨⟨x, hx⟩, hxy⟩ hy3
    exact ⟨u, subset_closure ⟨u.property, (Subgroup.orderOf_coe u).trans hu3⟩, hu⟩

theorem starImage_theta [Finite G] (H L : Subgroup G) (hLH : L ≤ H) :
    starImage H (theta L) = theta (starImage H L) := by
  have ht : (theta L).subgroupOf H = theta (L.subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((theta_le L).trans hLH),
      theta_map_of_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hLH]
  unfold starImage
  rw [ht]
  apply theta_map_of_twoGroup_ker
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

private theorem card_three_le_theta (R L : Subgroup G)
    (hR : Nat.card R = 3) (hRL : R ≤ L) : R ≤ theta L := by
  intro r hr
  have hd : orderOf (⟨r, hr⟩ : R) ∣ 3 := hR ▸ orderOf_dvd_natCard (⟨r, hr⟩ : R)
  rw [← Subgroup.orderOf_coe] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · change orderOf r = 1 at h1
    rw [orderOf_eq_one_iff.mp h1]
    exact one_mem _
  · exact subset_closure ⟨hRL hr, h3⟩

theorem theta_escape_of_star_three_subgroup [Finite G]
    (H L Y0 : Subgroup G) (hLH : L ≤ H)
    (R : Subgroup (H ⧸ pCore 2 H)) (hR : Nat.card R = 3)
    (hRL : R ≤ starImage H L) (hescape : ¬ R ≤ starImage H Y0) :
    ¬ theta L ≤ Y0 := by
  intro htheta
  apply hescape
  have hRtheta := card_three_le_theta R (starImage H L) hR hRL
  rw [← starImage_theta H L hLH] at hRtheta
  exact hRtheta.trans (map_mono (comap_mono htheta))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration

