module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Equivariant changes of coordinates on binary sections

A representation equivalence changes the coordinates of an actual subgroup
section while retaining its actor map, literal kernel and ambient inclusions.
This transports the original A₅ section to the two concrete module models
in Aschbacher–Smith, 10.1.1, printed p.741.
-/

@[expose] public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G J W U : Type*} [Group G] [Group J]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
  {H A B : Subgroup G} {ρ : Representation (ZMod 2) J W}
  {σ : Representation (ZMod 2) J U} (q : H →* J)

/-- Change module coordinates without changing the literal subgroup section. -/
def relabel (c : BinaryConjugationSection H A B (ρ.comp q)) (E : ρ.Equiv σ) :
    BinaryConjugationSection H A B (σ.comp q) where
  section_le := c.section_le
  kernel_le := c.kernel_le
  normalized := c.normalized
  coordinates := E.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp c.coordinates
  onto := E.toLinearEquiv.toAddEquiv.toMultiplicative.surjective.comp c.onto
  kernel_eq := by
    ext a
    change E (c.coordinates a).toAdd = 0 ↔ (a:G) ∈ B
    rw [← c.coordinates_eq_one_iff a]
    change E (c.coordinates a).toAdd = 0 ↔ (c.coordinates a).toAdd = 0
    exact E.toLinearEquiv.map_eq_zero_iff
  equivariant h a := by
    change E (c.coordinates _).toAdd = σ (q h) (E (c.coordinates a).toAdd)
    rw [c.equivariant]
    exact IntertwiningMap.isIntertwining ρ σ E.toIntertwiningMap (q h) (c.coordinates a).toAdd
end Representation.BinaryConjugationSection
