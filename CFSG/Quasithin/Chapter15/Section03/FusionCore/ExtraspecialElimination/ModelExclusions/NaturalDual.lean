module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Coordinates for the exceptional natural-plus-dual section

The natural action is the actual matrix action of PSL₄(2), through the
proved SL/PSL/linear comparison. The dual is contragredient. Coordinates
for `Ũ₀` must intertwine the action of the actual star component; the
submodule is identified with `[Ũ_H,L*]`, not an unrelated representation.

These definitions specify the remaining middle-node calculation. They do
not assert that the coordinates exist or that its point-core has no offender.
Those are the B.5.1 reduction and B.4.9(2iii) application on printed p.1145
of Aschbacher–Smith, combined manuscript (1 March 2004).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions

open Chapter2.ComponentRefinement.LieType.Binary

namespace BinaryGeometry

/-- The natural matrix representation of the actual projective carrier. -/
noncomputable def natural (n : ℕ) [NeZero n] :
    Representation (ZMod 2) (PSL n) (Vector n) where
  toFun g := (pslEquivLinear n g).toLinearMap
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

/-- The direct sum with its contragredient, retaining both summands. -/
noncomputable def naturalDual (n : ℕ) [NeZero n] :
    Representation (ZMod 2) (PSL n)
      (Vector n × Module.Dual (ZMod 2) (Vector n)) :=
  (natural n).prod (natural n).dual

theorem natural_project (n : ℕ) [NeZero n] (g : SL n) (v : Vector n) :
    natural n (QuotientGroup.mk' (Subgroup.center (SL n)) g) v = Matrix.mulVec g.val v :=
  pslEquivLinear_project n g v

end BinaryGeometry

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- Coordinates on the actual component commutator submodule. Restricting
the whole actor to its specified component appears explicitly in equivariance. -/
structure NaturalDualCoordinates (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) (e : L ≃* PSL 4) (U₀ : Subrepresentation ρ) where
  component_space : U₀.toSubmodule = Representation.Coinvariants.ker (ρ.comp L.subtype)
  coordinates : U₀.toSubmodule ≃ₗ[ZMod 2]
    (Vector 4 × Module.Dual (ZMod 2) (Vector 4))
  equivariant : ∀ (g : L) v,
    coordinates (U₀.toRepresentation g v) = BinaryGeometry.naturalDual 4 (e g) (coordinates v)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
