module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The linear automorphism group of a binary four-space

A basis identifies the linear automorphisms with GL₄(2). Binary units have
trivial determinant, and SL₄(2) has trivial scalar center. Composing these
actual maps with the exterior-square comparison gives GL(V) ≃ A₈. In
particular, inner conjugations on the A₈ side pull back to conjugations by
linear automorphisms of V.

The exceptional comparison is the port of Gerald Höhn and ATLAS contributors
in `Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`, retaining the
ATLAS Research and Attribution License 1.0 (`LICENSES/ATLAS.txt`). This
adapter supplies the linear-group interface used in Aschbacher–Smith,
K.1.1, printed p.452.
-/

public section

namespace BinaryFourAlternatingEight
open scoped MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

noncomputable def linearEquivAlternatingEight (hd : Module.finrank (ZMod 2) V = 4) :
    (V ≃ₗ[ZMod 2] V) ≃* alternatingGroup (Fin 8) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    ((Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq (ZMod 2) V hd)).symm.trans
      ((MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
        ⟨Matrix.SpecialLinearGroup.toGL_injective,
          BinaryLinear.OuterCyclic.binary_toGL_surjective 4⟩).symm.trans
        (Atlas.Order20160A8.sl4TwoEquivPSL.trans
          Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)))

end BinaryFourAlternatingEight
