module
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Relative centralizers under injective homomorphisms

An injective homomorphism preserves the centralizer of one subgroup inside
another. The forward inclusion reflects commutation by injectivity; the
reverse inclusion maps the original commuting pairs.

This common interface is used by the central-cover Sylow actors in
Aschbacher–Smith 2.5.7 and the elementary-eight point images in 15.1.11.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- An embedding preserves the centralizer of a subgroup inside a specified subgroup. -/
theorem map_inf_centralizer_of_injective (f : G →* H) (hf : Function.Injective f)
    (S E : Subgroup G) :
    S.map f ⊓ centralizer (E.map f : Set H) = (S ⊓ centralizer (E : Set G)).map f := by
  ext y
  constructor
  · rintro ⟨⟨s,hs,rfl⟩,hc⟩
    refine ⟨s,⟨hs,?_⟩,rfl⟩
    intro x hx
    apply hf
    simpa only [map_mul] using hc (f x) (mem_map_of_mem f hx)
  · rintro ⟨s,⟨hs,hc⟩,rfl⟩
    refine ⟨mem_map_of_mem f hs,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    simpa only [map_mul] using congrArg f (hc x hx)

end Subgroup
