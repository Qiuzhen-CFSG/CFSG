module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Centralizers
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.CentralCoprimePrimeLift

/-!
# Cubic centralizers from involution fibers

Transitivity in an involution fiber makes the centralizer surject onto the
centralizer in the actor quotient. An odd subgroup lifts through its two-group
kernel. A further central two-kernel has exact centralizer transport for this
odd subgroup, giving a cubic subgroup centralized by the original involution.

This isolates the two quotient steps used with `H/Z` and `H/U`; it does not
assume a centralized cubic lift or an involution nonfusion assertion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G Q R : Type*} [Group G] [Group Q] [Group R]

/-- Transitivity in the involution fiber makes the centralizer map onto the
centralizer of the image. -/
theorem centralizer_image_of_involution_fiber (f : G →* Q)
    (hf : Function.Surjective f) (t : G) (ht : t ^ 2 = 1)
    (horbit : ∀ x : G, x ^ 2 = 1 → f x = f t →
      ∃ u ∈ f.ker, u⁻¹ * t * u = x) :
    (centralizer ({t} : Set G)).map f = centralizer ({f t} : Set Q) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx)
  · intro a ha
    obtain ⟨h, rfl⟩ := hf a
    have hsq : (h * t * h⁻¹) ^ 2 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, ht, map_one]
    have hsame : f (h * t * h⁻¹) = f t := by
      rw [map_mul, map_mul, map_inv, mem_centralizer_singleton_iff.mp ha]
      simp only [mul_inv_cancel_right]
    obtain ⟨u, hu, he⟩ := horbit (h * t * h⁻¹) hsq hsame
    refine ⟨u * h, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hh := congrArg (fun b => u * b * h) he
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm
    · rw [map_mul, MonoidHom.mem_ker.mp hu, one_mul]

/-- Lift a cubic subgroup of the actor centralizer through the elementary
quotient and then the central two-kernel. No centralizing lift is assumed. -/
theorem exists_cubic_in_centralizer_of_involution_fiber [Finite G] [Finite Q] [Finite R]
    (f : G →* Q) (hf : Function.Surjective f)
    (hfcentral : f.ker ≤ center G) (hfker : IsPGroup 2 f.ker)
    (g : Q →* R) (hg : Function.Surjective g) (hgker : IsPGroup 2 g.ker)
    (t : G) (ht : t ^ 2 = 1)
    (horbit : ∀ x : Q, x ^ 2 = 1 → g x = g (f t) →
      ∃ u ∈ g.ker, u⁻¹ * f t * u = x)
    (D : Subgroup R) (hD : Nat.card D = 3)
    (hDC : D ≤ centralizer ({g (f t)} : Set R)) :
    ∃ E : Subgroup G, Nat.card E = 3 ∧ E ≤ centralizer ({t} : Set G) ∧
      (E.map f).map g = D := by
  let C := centralizer ({f t} : Set Q)
  let C' := centralizer ({g (f t)} : Set R)
  have hmap : C.map g = C' := centralizer_image_of_involution_fiber g hg (f t)
    (by rw [← map_pow, ht, map_one]) horbit
  let k : C →* C' := (g.comp C.subtype).codRestrict C' (fun x => hmap ▸ mem_map_of_mem g x.property)
  have hk : Function.Surjective k := by
    intro d
    obtain ⟨x, hx, he⟩ := show (d : R) ∈ C.map g from hmap.symm ▸ d.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hker : k.ker = g.ker.subgroupOf C := by
    ext x
    change k x = 1 ↔ g x = 1
    exact Subtype.ext_iff
  have hk2 : IsPGroup 2 k.ker := hker ▸ hgker.comap_subtype
  have hcD : Nat.card (D.subgroupOf C') = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hD
  obtain ⟨E0, he0, _, hc0, _⟩ := k.exists_odd_subgroup_lift hk hk2 (D.subgroupOf C')
    (by rw [hcD]; decide)
  let Ebar := E0.map C.subtype
  have hcbar : Nat.card Ebar = 3 := by
    rw [card_map_of_injective C.subtype_injective, hc0, hcD]
  have hbar : IsPGroup 3 Ebar := IsPGroup.of_card (n := 1) (by simpa using hcbar)
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hfker.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨E, _, he, _, hcent, hinj⟩ :=
    exists_prime_lift_of_central_coprime f hf hfcentral hcop Ebar hbar
  have hcE : Nat.card E = 3 := by
    have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, range_subtype, he, hcbar] at hc
    exact hc
  have htE : t ∈ centralizer (E : Set G) := by
    rw [← hcent]
    change f t ∈ centralizer (Ebar : Set Q)
    intro x hx
    exact mem_centralizer_singleton_iff.mp (map_subtype_le E0 hx)
  refine ⟨E, hcE, ?_, ?_⟩
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (htE x hx)
  · rw [he]
    have hh := congrArg (Subgroup.map C'.subtype) he0
    rw [map_map, map_subgroupOf_eq_of_le hDC] at hh
    exact (map_map ..).trans hh

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
