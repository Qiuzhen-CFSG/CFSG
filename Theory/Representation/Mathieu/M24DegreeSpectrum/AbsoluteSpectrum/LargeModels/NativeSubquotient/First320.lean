module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320.Coordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320.GeneratorA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320.GeneratorB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Models

/-!
# Both degree-320 modules on native M24

The saved nonzero embedding intertwines the two native tensor generators with
A and B squared. Density makes it injective. Restricting the native tensor
action to its image constructs 320a, and the checked literal contragredient
identities construct 320b. The public inverse-generator convention is retained.
The binary pair then consumes the existing density and trace separation.

Source: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
Aschbacher–Smith K.4, printed p.457. Witness provenance and ATLAS attribution:
First320/source/README.md.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
namespace NativeSubquotient.First320
open TensorCoordinates

/-- A single checked entry certifies nonvanishing; no inverse map is needed. -/
theorem embedding_ne_zero : Matrix.toLin' embedding ≠ 0 := by
  intro h
  have hm : embedding = 0 := by
    simpa only [LinearMap.toMatrix'_toLin', map_zero] using congrArg LinearMap.toMatrix' h
  have hv : embedding 0 2 = 1 := by decide +kernel
  have he := congrArg (fun M : Matrix (Fin 484) (Fin 320) (ZMod 2) => M 0 2) hm
  rw [hv, Matrix.zero_apply] at he
  exact one_ne_zero he

theorem embedding_first :
    (action484 Degree220Pair.generatorA).comp (Matrix.toLin' embedding) =
      (Matrix.toLin' embedding).comp (Matrix.toLin' (Degree320Pair.matrixA false)) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', native_matrix_A,
    ← target_matrix_A]
  exact embedding_A

theorem embedding_second :
    (action484 Degree220Pair.generatorB).comp (Matrix.toLin' embedding) =
      (Matrix.toLin' embedding).comp (Matrix.toLin' (Degree320Pair.matrixB false ^ 2)) := by
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', native_matrix_B,
    ← target_matrix_B]
  exact embedding_B

/-- The first raw ATLAS pair acts at the inverse native generators. -/
theorem nativeRealization :
    ∃ ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 Degree320Pair.Space,
      Degree320Pair.Realizes false ρ := by
  obtain ⟨ρ, hA, hB⟩ := of_embedding action484 _ _ (Matrix.toLin' embedding)
    (Degree320Pair.first_embedding_injective action484 (Matrix.toLin' embedding)
      embedding_ne_zero embedding_first embedding_second) embedding_first embedding_second
  exact ⟨ρ, Degree320Pair.realizes_of_positive_generator_matrices false ρ hA hB⟩

/-- Both literal 320-dimensional actions, with no presentation premise. -/
theorem actionsExist : Degree320Pair.ActionsExist := by
  obtain ⟨ρ, hρ⟩ := nativeRealization
  exact Degree320Pair.actionsExist_of_first_action ρ hρ

end NativeSubquotient.First320

/-- The two inequivalent absolutely irreducible binary degree-320 models on
the actual native Witt-design M24. -/
theorem pair320 : Nonempty (BinaryPair 320) :=
  pair320_of_certificates NativeSubquotient.First320.actionsExist
    Degree320Pair.generatorDensity Degree320Pair.traceSeparation

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
