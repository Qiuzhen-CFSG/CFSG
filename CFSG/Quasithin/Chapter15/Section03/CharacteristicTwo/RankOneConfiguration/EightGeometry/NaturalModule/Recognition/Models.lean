module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Basic

/-!
# The two module alternatives and the actual middle-node marking

The orthogonal alternative is a central covering of the six-dimensional
binary permutation module, with an equivariant surjection and its precise
fixed-space kernel. It does not assert that the kernel vanishes. The other
alternative is the actual four-dimensional projective linear action plus
its contragredient. Both concern the entire component commutator module.

The component parabolic is an actual flag stabilizer with dimensions one
and three, using the same projective-linear identification as the module.
It is kept separate from its extension by the Sylow subgroup in `S₈`.

These are outputs to be constructed from B.5.1, not assumed classifications
or proofs of 15.3.32. They give independent classification and geometric
exclusion arguments a common mathematical interface.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1),
15.3.28(3), and 15.3.32(1), printed pp.99, 1131–1133.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition
namespace Models
open Chapter2.ComponentRefinement.LieType.Binary
open Representation.BinaryOffender

/-- The actual natural representation of `PSL₄(2)`. -/
noncomputable def naturalFour : Representation (ZMod 2) (PSL 4) (Vector 4) where
  toFun g := (pslEquivLinear 4 g).toLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

/-- The sum of the natural representation and its contragredient. -/
noncomputable def naturalDualFour : Representation (ZMod 2) (PSL 4)
    (Vector 4 × Module.Dual (ZMod 2) (Vector 4)) :=
  naturalFour.prod naturalFour.dual

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- A projective line is a binary space of order four. The actual parabolic
and Sylow subgroup preserve it, and the specified subgroup has no nonzero
fixed vector on it. This is geometry to be constructed from `V₂`, not a
recognition hypothesis. -/
structure MovingLine (ρ : Representation (ZMod 2) K V) (P S Y : Subgroup K) where
  space : Submodule (ZMod 2) V
  card : Nat.card space = 4
  parabolic_stable : ∀ p ∈ P, ∀ v ∈ space, ρ p v ∈ space
  sylow_stable : ∀ s ∈ S, ∀ v ∈ space, ρ s v ∈ space
  fixed_disjoint : Disjoint space (fixedSpace ρ Y)

/-- The marked component intersection in 15.3.28(3). The full Sylow extension
is not equated with this subgroup of the alternating component. -/
structure MiddleNodeMarking (L P : Subgroup K) where
  model : L ≃* PSL 4
  flag : Flag 4
  middle : flag.types = {1, 3}
  parabolic : P = ambientFlagStabilizer model flag

/-- A central cover of the orthogonal module. Equivariance is required only
for the actual component; extending it to all of `S₈` is a later obligation. -/
structure OrthogonalCover (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) (e : K ≃* Equiv.Perm (Fin 8)) where
  projection : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)
  onto : Function.Surjective projection
  equivariant : ∀ (l : L) v, projection (ρ l v) =
    BinaryPermutation.naturalRepresentation (Fin 8) (e l) (projection v)
  kernel : projection.ker = fixedSpace ρ L
  generated : Representation.Coinvariants.ker (ρ.comp L.subtype) = ⊤

/-- Natural-plus-dual coordinates in precisely the projective-linear
marking used to describe the component parabolic. -/
structure NaturalDual (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) (model : L ≃* PSL 4) where
  coordinates : V ≃ₗ[ZMod 2] (Vector 4 × Module.Dual (ZMod 2) (Vector 4))
  equivariant : ∀ (l : L) v, coordinates (ρ l v) =
    naturalDualFour (model l) (coordinates v)

/-- The reduced alternatives on the full component module. Proving this
disjunction from the universal FF theorem is a separate task. -/
def Alternatives (ρ : Representation (ZMod 2) K V) (L P : Subgroup K)
    (e : K ≃* Equiv.Perm (Fin 8)) (mark : MiddleNodeMarking L P) : Prop :=
  Nonempty (OrthogonalCover ρ L e) ∨ Nonempty (NaturalDual ρ L mark.model)

end Models
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

end
