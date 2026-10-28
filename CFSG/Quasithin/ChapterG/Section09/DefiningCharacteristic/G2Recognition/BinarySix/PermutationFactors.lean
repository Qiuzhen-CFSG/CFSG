module

public import Theory.Representation.G2DerivedSixFactorMaps

/-!
# Concrete six-dimensional factor maps for the binary G₂ recognition argument

Every six-dimensional simple factor in the actual derived-group flag module
has a nonzero intertwining map to the actual natural coordinate action. The
lower-layer proof uses the completed parabolic and boundary-kernel filtrations,
with explicit binary maps on their literal quotients and the proved generation
of the entire commutator group.

This discharges the concrete filtration premise of
`BinarySix.quasiequivalent_of_permutation_factor_maps`. The parent module owns
recognition assembly for Aschbacher--Smith G.9.3(10), printed pp.354,356--357.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix

/-- Unconditional natural-coordinate maps on every degree-six simple factor
of the concrete G₂(2)′ flag permutation module. -/
theorem flag_factorMapFiltration :
    Representation.FactorMapFiltration Atlas.G2.Natural.Binary.coordinateAction
      G2DerivedPermutationFiltration.flagRepresentation :=
  G2DerivedSixFactorMaps.flag_factorMapFiltration

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
