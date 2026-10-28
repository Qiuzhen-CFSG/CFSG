module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.Flag
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.Assembly
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.SavedComparison

/-!
# Native/saved Hermitian generator comparison

The literal right-coset action of the native M22 generators is equivalent to
saved GAP orientation zero. The section change first replaces the chosen coset
representatives equivariantly. The uniform Hermitian marking change and the
certified SL correction lifts then identify its blocks with the executable
nine-dimensional Hermitian matrices. Finally, the checked inverse and
intertwining matrices identify these native blocks with the saved columns.

All comparison premises are discharged here, including the noncomputably chosen
point-stabilizer marking. The index labels a saved GAP orientation, not a choice
between the Hermitian point module and its dual. The resulting literal flag is
also constructed; factor irreducibility remains with the filtration consumer.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452,457.
-/

public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration

namespace NativeComparison

/-- The certified native corrections act by the executable Hermitian blocks,
after the same marking and binary coordinate change in every fiber. -/
theorem nativeBlocks_action (j : Fin 2) (p : Fin 22) (v : Models.HermitianSpace) :
    nativeCoordinates HermitianCoordinates.binaryCoordinates
      (Models.pointAction false (SixteenSubmodule.GeneratorMatrices.generatorCorrection j p) v) =
      (nativeBlocks j p).mulVec (nativeCoordinates HermitianCoordinates.binaryCoordinates v) :=
  HermitianCoordinates.correction_blocks
    SixteenSubmodule.LocalBlocks.correctionLift SixteenSubmodule.LocalBlocks.correctionMatrix
    SixteenSubmodule.LocalBlocks.correctionLift_embedding
    SixteenSubmodule.LocalBlocks.correctionLift_pointwiseEquiv j p v

/-- The native induced coordinates intertwine both literal generators with
saved orientation zero, with every block and similarity premise discharged. -/
theorem generator_coordinates :
    ∃ e : CoordinateSpace false ≃ₗ[ZMod 2] Space,
      ∀ (j : Fin 2) v, e (coordinateAction false (actor j) v) =
        (generatorMatrix SavedComparison.orientation j).mulVec (e v) :=
  generator_coordinates_of_block_certificates
    (nativeCoordinates HermitianCoordinates.binaryCoordinates) nativeBlocks nativeBlocks_action
    SavedComparison.orientation SavedComparison.C SavedComparison.D
    SavedComparison.D_mul_C SavedComparison.C_mul_D SavedComparison.generators

end NativeComparison

/-- Exact comparison premise for `filtration_of_generator_coordinates`, for
the literal Hermitian induction and the saved generator matrices. -/
theorem exists_generator_coordinates :
    ∃ i : Fin 2, ∃ e : CoordinateSpace false ≃ₗ[ZMod 2] Space,
      ∀ (j : Fin 2) v, e (coordinateAction false (actor j) v) =
        (generatorMatrix i j).mulVec (e v) :=
  ⟨NativeComparison.SavedComparison.orientation, NativeComparison.generator_coordinates⟩

/-- The comparison supplies the actual invariant flag and its literal quotient
coordinates. No factor-density premise is needed for this construction. -/
theorem native_flag_coordinates :
    Nonempty (FlagCoordinates NativeComparison.SavedComparison.orientation) := by
  obtain ⟨e, he⟩ := NativeComparison.generator_coordinates
  exact ⟨flagOfGeneratorCoordinates _ e he⟩

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
