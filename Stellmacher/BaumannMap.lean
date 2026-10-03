module

public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.OmegaOneCenterMap

/-!
# Injective transport of the Baumann subgroup

An injective homomorphism carries the relative Baumann subgroup
C_Q(Ω₁(Z(J(Q)))) to the same expression formed in the image of Q.
The result does not require either ambient group to be finite.

The elementary Thompson subgroup and its central involutions commute
with injective maps by the imported transport theorems. Injectivity then
identifies commuting pairs in the relative centralizer. This supplies the
native-to-ambient subgroup equality for applications of Stellmacher (2.3)
in (4.6) and (6.1), without importing either later section.

Source: Stellmacher, Journal of Algebra 190 (1997), the Baumann notation
and Sylow transports in (4.6), p26, and (6.1), p30.
-/

namespace Stellmacher

/-- The exact Baumann expression commutes with the injective native-to-ambient map. -/
public theorem baumann_map_injective
    {H G : Type*} [Group H] [Group G] (f : H →* G) (hf : Function.Injective f)
    (Q : Subgroup H) :
    (Q ⊓ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set H)).map f =
      Q.map f ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q.map f)) : Set G) := by
  let W := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have hW : W.map f = omegaOneCenterAmbient (elementaryAbelianMaxJ (Q.map f)) := by
    rw [elementaryAbelianMaxJ_map_injective f hf Q]
    exact (omegaOneCenterAmbient_map_injective f hf _).symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hy.1, ?_⟩
    change f y ∈ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q.map f)) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hW] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp hy.2 w hw)
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    change y ∈ Subgroup.centralizer (W : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    apply hf
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hc (f w)
      (by rw [← hW]; exact Subgroup.mem_map_of_mem f hw)

end Stellmacher
