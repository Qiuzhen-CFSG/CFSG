module

public import Theory.SpecificGroups.BabyMonster.NormalSubgroups.Generation
public import Theory.SpecificGroups.BabyMonster.Order.Bounds

/-!
# Transport of the local center calculation to the fixed presentation

A verified image of the presentation, of at least the prescribed order, is
faithful once the carrier has that order. A bijection then identifies the
centralizers of corresponding generators and transports their centers. Thus a
local calculation in an explicit image suffices for the fixed presented carrier.

The intended image and local calculation are described in §§3.2–3.4 and 5.1 of
Breuer–Magaard–Wilson, *Verification of the ordinary character table of the Baby
Monster*, J. Algebra 534 (2019), https://arxiv.org/abs/1902.07758.
The image-size bound and the local center calculation remain explicit premises
here; this module does not assert the unproved local structure of that image.
-/

public section
namespace BabyMonster

/-- An image of the prescribed size is faithful, assuming the prescribed order
of the fixed carrier. No simplicity hypothesis is needed. -/
theorem injective_of_card_range_ge [Finite Carrier] {G : Type*} [Group G]
    (hcard : Nat.card Carrier = 4154781481226426191177580544000000)
    (f : Carrier →* G)
    (hsize : 4154781481226426191177580544000000 ≤ Nat.card f.range) :
    Function.Injective f := by
  apply MonoidHom.rangeRestrict_injective_iff.mp
  exact (f.rangeRestrict_surjective.bijective_of_nat_card_le (hcard ▸ hsize)).1

/-- A verified family of generators of sufficiently large image yields a
faithful realization of the fixed presentation. -/
theorem lift_injective_of_card_generated_ge [Finite Carrier] {G : Type*} [Group G]
    (hcard : Nat.card Carrier = 4154781481226426191177580544000000)
    {t : Generator → G} (h : Relations t)
    (hsize : expectedOrder ≤ Nat.card (Subgroup.closure (Set.range t))) :
    Function.Injective (lift h) := by
  apply injective_of_card_range_ge hcard
  simpa only [range_lift, expectedOrder_decimal] using hsize

/-- Transport the local center bound along a bijective homomorphism from the
fixed presentation. The centralizer is taken inside the image group. -/
theorem generatorCentralizer_center_cases_of_bijective {G : Type*} [Group G]
    (f : Carrier →* G) (hf : Function.Bijective f)
    (hcenter : ∀ z : Subgroup.centralizer ({f (generator 0)} : Set G),
      z ∈ Subgroup.center (Subgroup.centralizer ({f (generator 0)} : Set G)) →
      (z : G) = 1 ∨ (z : G) = f (generator 0)) :
    ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : Carrier) = 1 ∨ (z : Carrier) = generator 0 := by
  intro z hz
  have hzf : f z ∈ Subgroup.centralizer ({f (generator 0)} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using
      congrArg f (Subgroup.mem_centralizer_singleton_iff.mp z.property)
  have hzcenter : (⟨f z, hzf⟩ : Subgroup.centralizer ({f (generator 0)} : Set G)) ∈
      Subgroup.center (Subgroup.centralizer ({f (generator 0)} : Set G)) := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    obtain ⟨x, hx⟩ := hf.2 (c : G)
    have hxC : x ∈ generatorCentralizer := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply hf.1
      simpa only [map_mul, hx] using
        Subgroup.mem_centralizer_singleton_iff.mp c.property
    apply Subtype.ext
    have heq := congrArg (fun y : generatorCentralizer => f (y : Carrier))
      (Subgroup.mem_center_iff.mp hz (⟨x, hxC⟩ : generatorCentralizer))
    simpa only [Subgroup.coe_mul, map_mul, hx] using heq
  rcases hcenter ⟨f z, hzf⟩ hzcenter with h | h
  · left
    apply hf.1
    simpa only [map_one] using h
  · exact Or.inr (hf.1 h)

/-- The local center calculation in a sufficiently large image implies the
desired bound in the fixed carrier. This separates the concrete image
calculation from presentation faithfulness. -/
theorem generatorCentralizer_center_cases_of_image [Finite Carrier]
    {G : Type*} [Group G]
    (hcard : Nat.card Carrier = 4154781481226426191177580544000000)
    (f : Carrier →* G)
    (hsize : 4154781481226426191177580544000000 ≤ Nat.card f.range)
    (hcenter : ∀ z : Subgroup.centralizer
        ({f.rangeRestrict (generator 0)} : Set f.range),
      z ∈ Subgroup.center (Subgroup.centralizer
        ({f.rangeRestrict (generator 0)} : Set f.range)) →
      (z : f.range) = 1 ∨ (z : f.range) = f.rangeRestrict (generator 0)) :
    ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : Carrier) = 1 ∨ (z : Carrier) = generator 0 := by
  apply generatorCentralizer_center_cases_of_bijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (injective_of_card_range_ge hcard f hsize),
      f.rangeRestrict_surjective⟩ hcenter

end BabyMonster
