module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarSpace

/-!
# Standard binary five-space as a line plus an alternating four-space

The displayed coordinates have columns `(1,1,1,1,1)`, `(1,1,0,0,0)`,
`(0,0,1,1,0)`, `(1,0,0,0,1)`, and `(1,1,1,0,1)`. Their dot-product
Gram matrix is `diag(1,J)` in the polar module's two-plus-two convention.
The finite coordinate identities are checked by kernel reduction.

Inverse transpose fixes precisely the dot-product isometries. In characteristic
two the all-ones vector represents the self-pairing functional, so every such
isometry fixes it. This prepares restriction to its alternating complement.

This is the standard fixed-group geometry used in Aschbacher–Smith, E.6.23,
printed p.254 (PDF p.265), `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix
open BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricSix

namespace BinaryLinear.SixSylowActors.Five.Standard
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

abbrev SplitSpace := ZMod 2 × NaturalModule

def join (x : SplitSpace) : Space 5 :=
  ![x.1 + x.2 (.inl 0) + x.2 (.inr 0) + x.2 (.inr 1),
    x.1 + x.2 (.inl 0) + x.2 (.inr 1),
    x.1 + x.2 (.inl 1) + x.2 (.inr 1),
    x.1 + x.2 (.inl 1),
    x.1 + x.2 (.inr 0) + x.2 (.inr 1)]

def split (x : Space 5) : SplitSpace :=
  (x 0 + x 1 + x 2 + x 3 + x 4,
   vec (x 0 + x 4) (x 0 + x 1 + x 2 + x 4) (x 0 + x 1) (x 2 + x 3))

def coordinates : SplitSpace ≃ₗ[ZMod 2] Space 5 where
  toFun := join
  invFun := split
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide
  map_smul' := by decide

theorem coordinates_form (x y : SplitSpace) :
    dotProduct (coordinates x) (coordinates y) = x.1 * y.1 + polarForm x.2 y.2 := by
  decide +revert

def canonical : Space 5 := fun _ => 1

theorem coordinates_one_zero : coordinates (1, 0) = canonical := by decide

theorem canonical_pair_self (x : Space 5) :
    dotProduct canonical x = dotProduct x x := by decide +revert

theorem fixed_iff_form (g : LinearGroup 5) :
    g ∈ (graphLinear 5).fixedSubgroup ↔
      ∀ x y, dotProduct (g x) (g y) = dotProduct x y := by
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · intro hg x y
    simpa only [hg] using graphLinear_dotProduct g x y
  · intro h
    apply LinearEquiv.ext
    intro x
    apply dotProduct_eq
    intro z
    obtain ⟨y, rfl⟩ := g.surjective z
    exact (graphLinear_dotProduct g x y).trans (h x y).symm

theorem fixed_canonical (g : (graphLinear 5).fixedSubgroup) :
    (g : LinearGroup 5) canonical = canonical := by
  have hg := (fixed_iff_form g.val).mp g.property
  apply dotProduct_eq
  intro z
  obtain ⟨x, rfl⟩ := g.val.surjective z
  rw [hg, canonical_pair_self, canonical_pair_self, hg]


end BinaryLinear.SixSylowActors.Five.Standard
