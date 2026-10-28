module

public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transport of uniform root centralizers

An injective embedding transports a centralizer calculation inside a specified
subgroup. No assertion is made about centralizers outside that subgroup: the
ambient group can have additional field automorphisms. The embedded center is
transported by `Subgroup.map_embeddedCenter`.

This is the group-theoretic transport used in Aschbacher–Smith, proof of 13.6.6,
printed p.927, after identifying the component and its Borel.
-/

public section
namespace Subgroup.NormalizedRootCentralizers
open Subgroup
variable {M H : Type*} [Group M] [Group H]

/-- Uniform centralizers transport to every subgroup of the specified image.
The embedding need not cover the ambient group. -/
theorem transport (f : M →* H) (hf : Function.Injective f)
    (B₀ R₀ : Subgroup M) (B R : Subgroup H)
    (hB : B ≤ B₀.map f) (hR : R = R₀.map f)
    (hroot : ∀ r ∈ R₀, r ≠ 1 →
      B₀ ⊓ centralizer ({r} : Set M) = B₀ ⊓ centralizer (R₀ : Set M))
    (r : H) (hr : r ∈ R) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set H) = B ⊓ centralizer (R : Set H) := by
  rw [hR] at hr ⊢
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  have hn₀ : r₀ ≠ 1 := fun he => hne (he ▸ f.map_one)
  apply le_antisymm
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hB hb.1
    have hc₀ : b₀ ∈ centralizer ({r₀} : Set M) := by
      apply mem_centralizer_singleton_iff.mpr
      apply hf
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hb.2
    have hc := (show b₀ ∈ B₀ ⊓ centralizer (R₀ : Set M) from
      hroot r₀ hr₀ hn₀ ▸ ⟨hb₀, hc₀⟩).2
    refine ⟨hb.1, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hc x hx)
  · exact inf_le_inf_left B (centralizer_le (Set.singleton_subset_iff.mpr
      (mem_map_of_mem f hr₀)))

/-- If nonidentity elements of U have their centralizers inside U, then
each nonidentity element of Z(U) has centralizer exactly U. -/
theorem centralizer_eq_of_center (U : Subgroup H)
    (hU : ∀ r ∈ U, r ≠ 1 → centralizer ({r} : Set H) ≤ U)
    (r : H) (hr : r ∈ (center U).map U.subtype) (hne : r ≠ 1) :
    centralizer ({r} : Set H) = U := by
  obtain ⟨r, hr, rfl⟩ := hr
  apply le_antisymm (hU r r.property hne)
  intro u hu
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mem_center_iff.mp hr ⟨u, hu⟩)

/-- The preceding structural criterion supplies the uniform root calculation,
even in the whole group rather than just its Borel. -/
theorem uniform_of_centralizer_le (U : Subgroup H)
    (hU : ∀ r ∈ U, r ≠ 1 → centralizer ({r} : Set H) ≤ U)
    (B : Subgroup H) (r : H) (hr : r ∈ (center U).map U.subtype) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set H) =
      B ⊓ centralizer (((center U).map U.subtype : Subgroup H) : Set H) := by
  have hc := centralizer_eq_of_center U hU r hr hne
  have hZ : centralizer (((center U).map U.subtype : Subgroup H) : Set H) = U := by
    apply le_antisymm
    · exact (centralizer_le (Set.singleton_subset_iff.mpr hr)).trans hc.le
    · intro u hu
      apply mem_centralizer_iff.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩).symm
  rw [hc, hZ]

end Subgroup.NormalizedRootCentralizers
