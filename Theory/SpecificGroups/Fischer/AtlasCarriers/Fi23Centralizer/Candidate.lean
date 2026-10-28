module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Evaluation

/-!
# The exact Fi23 involution and its fixed coordinates

For the literal ATLAS generators, the seventh power of
`(a*b^2)*(a*b^2)*(a*b)^3` has square one and moves zero to 15180.
Its fixed letters are exactly the range of the existing 3511-coordinate map.
Kernel-checked cycle and lookup certificates supply all permutation identities.
This discharges the candidate and coordinate premises of the fixed-point image
construction; identifying that image and the whole centralizer is separate.

Source: GLS3 Table 5.3u and the Fischer paragraph in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1042; exact permutation data:
ATLAS `F23G1-p31671B0.g1` and `.g2` in `AtlasCarriers/source/`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open CandidateCertificate

/-- A moved letter witnesses that the concrete candidate is nonidentity. -/
theorem candidate_zero : inclusion candidate (0 : Fin 31671) = 15180 := by
  rw [candidate_apply]
  decide +kernel

private theorem order_two_of_faithful_action {G α : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (hρ : Function.Injective ρ) (g : G)
    (hsq : ∀ x, ρ g (ρ g x) = x) (x : α) (hm : ρ g x ≠ x) :
    orderOf g = 2 := by
  apply orderOf_eq_prime
  · apply hρ
    rw [map_pow, map_one]
    apply Equiv.ext
    intro y
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using hsq y
  · intro h
    apply hm
    rw [h, map_one]
    rfl

/-- The specified word defines a genuine involution of the exact ATLAS carrier. -/
theorem candidate_order : orderOf candidate = 2 := by
  apply order_two_of_faithful_action inclusion inclusion_injective candidate
    (x := (0 : Fin 31671))
  · intro x
    rw [candidate_apply, candidate_apply]
    exact cMap_involution x
  · rw [candidate_zero]
    decide

/-- Precisely the supplied 3511 coordinates, including letter 15181, are fixed. -/
theorem candidate_fixed_iff : ∀ x : Fin 31671,
    inclusion candidate x = x ↔ x ∈ Set.range ImageData.point := by
  intro x
  rw [candidate_apply, cMap_fixed]
  have hc : ImageData.point (ImageData.coordinate x) =
      ImageData.pointIndex (ImageData.index x) := by
    simp only [ImageData.point, ImageData.coordinate, Equiv.symm_apply_apply]
  rw [← hc]
  constructor
  · intro h
    exact ⟨ImageData.coordinate x, h⟩
  · rintro ⟨i, rfl⟩
    rw [ImageData.coordinate_point]

end Sporadic.Fischer.Fi23.CentralizerSection
