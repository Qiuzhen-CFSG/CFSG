module

public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Maximality

/-!
# The even four-block subgroup as an end-node parabolic

The actual ATLAS exceptional equivalence sends the stabilizer of the
unordered partition {0123,4567} in A₈ to the stabilizer of a binary two-plane.
The geometric comparison uses the exterior vector e₀ ∧ e₁ and the deleted
class of 11110000. The independent index argument proves maximality in A₈.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.32(4), printed pp.1132–1133. The licensed ATLAS construction and its
attribution are retained in the `Geometry` descendant.
-/

namespace Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
open A6ShadowTwoLocals

/-- Complete witnesses for the marked two-plane parabolic, including maximality in A₈. -/
public theorem exists_model :
    ∃ (j : A8 ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
      (W : Submodule (ZMod 2) (Fin 4 → ZMod 2)),
      Module.finrank (ZMod 2) W = 2 ∧
      (BinaryLinear.parabolic W).comap j.toMonoidHom = fourStabilizer.subgroupOf A8 ∧
      IsCoatom (fourStabilizer.subgroupOf A8) :=
  ⟨equiv, plane, plane_finrank, parabolic_comap, fourStabilizer_subgroupOf_isCoatom⟩

end Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
