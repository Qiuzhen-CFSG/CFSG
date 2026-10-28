module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Models

/-!
# Transporting the exterior-square obstruction to the actual head

The image of the generating seed in a proper quotient has binary dimension
exactly two. An equivariant exterior-square identification would therefore
produce a two-dimensional invariant subspace for the full marked parabolic.
This lemma transports an intrinsic obstruction for that concrete action to
an exclusion of the head; it does not assume the exclusion of any chief factor.

The intrinsic exterior-square obstruction remains an explicit premise. It must
be proved before this reduction can complete the source argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.960 (PDF p.977).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
open Representation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

theorem not_exteriorSquare_head_of_plane_obstruction
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (hgeometry : ∀ S : Submodule (ZMod 2) ExteriorSquare,
      Module.finrank (ZMod 2) S = 2 →
      (∀ g ∈ BinaryLinear.parabolic P, ∀ v ∈ S,
        exteriorPower.map 2 g.toLinearMap v ∈ S) → False)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    ¬ IsExteriorSquare W.quotientRepresentation eH := by
  rintro ⟨e, he⟩
  apply hgeometry (LinearMap.range (seedMap ρ s W e))
    (seedMap_range_finrank ρ s W hW e)
  intro g hg v hv
  rw [← hP] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  exact seedMap_range_stable ρ s W e (exteriorSquareAction eH) he a ha v hv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
