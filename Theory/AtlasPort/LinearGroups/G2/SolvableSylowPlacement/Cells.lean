module

public import Theory.AtlasPort.LinearGroups.G2.Borel
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps

/-!
# The twelve concrete G₂ Weyl cells

The representatives are the alternating words in the two displayed octonion
Weyl automorphisms, ordered by length. `BruhatCover` asks only for existence
of a factorization `u * w * t * v`, with both outer factors in the six positive
root groups and the torus factor in the actual split torus. No uniqueness or
restricted right-root factor is required by the solvable-overgroup argument.

This module defines the remaining geometric input; it does not prove that
the cells cover the automorphism group. The source is GLS III, Theorem 2.3.5
(`refs/KGroup/GLS3/chapter2.tex`), used for the larger-field Borel placement
on Aschbacher–Smith, printed p.1144. The concrete model and generators are
from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.SolvableSylowPlacement

variable {F : Type*} [Field F]

/-- Alternating representatives of the twelve elements of the G₂ Weyl group. -/
def weylRep (i : Fin 12) : Model F :=
  ![1, weylR, weylS, weylR * weylS, weylS * weylR,
    weylR * weylS * weylR, weylS * weylR * weylS,
    weylR * weylS * weylR * weylS, weylS * weylR * weylS * weylR,
    weylR * weylS * weylR * weylS * weylR,
    weylS * weylR * weylS * weylR * weylS,
    weylR * weylS * weylR * weylS * weylR * weylS] i

@[simp] theorem weylRep_zero : weylRep (F := F) 0 = 1 := rfl

/-- Existence of the concrete unipotent–Weyl–torus–unipotent factorization. -/
def BruhatCover (F : Type*) [Field F] : Prop :=
  ∀ g : Model F, ∃ (i : Fin 12) (u : Model F), u ∈ unipotent ∧
    ∃ t ∈ splitTorus, ∃ v ∈ unipotent, g = u * weylRep i * t * v

end Atlas.G2.SolvableSylowPlacement
