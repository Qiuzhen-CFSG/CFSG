module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Largest1792.Transport
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Rank
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Projection
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.NonzeroQuotient
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Source
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

/-!
# All eight large native Mathieu models

The native tensor subquotients supply the degree-320 pair and both largest
models on the Witt-design carrier. Their proved density and trace separation,
together with the native 120, 220 and 252 constructions, give all eight models
over every coefficient universe. `largeModelsExist` has no remaining matrix
certificate or presentation premise. The earlier conditional APIs are retained.

The degree-320 models retain raw matrices at inverse native generators; the
1242 and 1792 models retain transposes at positive native generators.
Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
Aschbacher–Smith K.4, p.457. ATLAS attribution is retained with the matrices.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
universe v
open Degrees12421792 NativeActions.Presentation

/-- All degree-320 matrix obligations are discharged; only native comparison remains. -/
theorem pair320_of_native_injective (hinj : Function.Injective toCarrier) :
    Nonempty (BinaryPair 320) :=
  pair320_of_certificates
    (Degree320Pair.actionsExist_of_relations hinj Degree320Pair.matrixRelations)
    Degree320Pair.generatorDensity Degree320Pair.traceSeparation

/-- Both largest models use their proved density and all seven matrix relations. -/
theorem models12421792_of_native_injective (hinj : Function.Injective toCarrier) :
    Nonempty (BinaryModel 1242) ∧ Nonempty (BinaryModel 1792) :=
  models12421792_of_matrix_certificates
    (native1242_of_relations hinj NativeActions.relations1242)
    (native1792_of_relations hinj NativeActions.relations1792) density1242 density1792

/-- The eight models over every coefficient universe from the single carrier comparison. -/
theorem largeModelsExist_of_native_injective (hinj : Function.Injective toCarrier) :
    LargeModelsExist.{v} := by
  obtain ⟨⟨a120⟩, ⟨a252⟩⟩ := models120252
  obtain ⟨a220⟩ := pair220
  obtain ⟨a320⟩ := pair320_of_native_injective hinj
  obtain ⟨⟨a1242⟩, ⟨a1792⟩⟩ := models12421792_of_native_injective hinj
  exact largeModelsExist_of_candidates a120 a252 a220 a320 a1242 a1792

/-- The literal finite presentation bound supplies exactly the remaining comparison. -/
theorem largeModelsExist_of_presentation_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040) :
    LargeModelsExist.{v} :=
  largeModelsExist_of_native_injective (toCarrier_injective_of_bound h)
/-- The proved native multiplier allows the relaxed double-order bound. -/
theorem largeModelsExist_of_double_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 489646080) :
    LargeModelsExist.{v} :=
  largeModelsExist_of_native_injective (toCarrier_injective_of_double_bound h)

/-- The max8 route needs only the first mixed identity and the outer coset cover;
all other representation, quartic and multiplier premises are discharged. -/
theorem largeModelsExist_of_first_and_cover
    (hf : OrderBound.LocalRelations.Mixed.FirstRelation)
    (cover : Subgroup.GeneratorCosetCover OrderBound.boundSubgroup
      OrderBound.generator (Fin 40320)) : LargeModelsExist.{v} :=
  largeModelsExist_of_native_injective (toCarrier_injective_of_first_and_cover hf cover)

/-- Native tensor construction discharges both degree-320 models. Only the
literal 1242 and 1792 native realizations remain; all density, separation,
small large-model and scalar-extension premises are supplied here. -/
theorem largeModelsExist_of_native_largest
    (h1242 : Nonempty (NativeRealization Data1242.first Data1242.second))
    (h1792 : Nonempty (NativeRealization Data1792.first Data1792.second)) :
    LargeModelsExist.{v} := by
  obtain ⟨r1242⟩ := h1242
  obtain ⟨r1792⟩ := h1792
  obtain ⟨⟨a120⟩, ⟨a252⟩⟩ := models120252
  obtain ⟨a220⟩ := pair220
  obtain ⟨a320⟩ := pair320
  obtain ⟨⟨a1242⟩, ⟨a1792⟩⟩ := models12421792_of_matrix_certificates
    r1242 r1792 density1242 density1792
  exact largeModelsExist_of_candidates a120 a252 a220 a320 a1242 a1792

/-- Assembly on the three genuine native tensor spaces. These are precisely
finite map obligations for the saved 1474/232 subquotient and 1792 quotient.
Density eliminates both right inverses; the 1474-dimensional source must still
be injectively and invariantly embedded. All four large models stay in this
assembly, and the 320 pair is already unconditional. -/
theorem largeModelsExist_of_tensor_maps
    (U₀ U₁ : Matrix (Fin 1474) (Fin 1474) (ZMod 2))
    (E : (Fin 1474 → ZMod 2) →ₗ[ZMod 2] (Fin 1936 → ZMod 2))
    (hE : Function.Injective E)
    (hEA : (NativeSubquotient.TensorCoordinates.action1936 Degree220Pair.generatorA).comp E =
      E.comp (Matrix.toLin' U₀))
    (hEB : (NativeSubquotient.TensorCoordinates.action1936 Degree220Pair.generatorB).comp E =
      E.comp (Matrix.toLin' U₁))
    (P : Matrix (Fin 1242) (Fin 1474) (ZMod 2)) (hP : Matrix.toLin' P ≠ 0)
    (hPA : P * U₀ = Data1242.first.transpose * P)
    (hPB : P * U₁ = Data1242.second.transpose * P)
    (Q : (Fin 2420 → ZMod 2) →ₗ[ZMod 2] (Fin 1792 → ZMod 2)) (hQ : Q ≠ 0)
    (hQA : Q.comp (NativeSubquotient.TensorCoordinates.action2420 Degree220Pair.generatorA) =
      (Matrix.toLin' Data1792.first.transpose).comp Q)
    (hQB : Q.comp (NativeSubquotient.TensorCoordinates.action2420 Degree220Pair.generatorB) =
      (Matrix.toLin' Data1792.second.transpose).comp Q) : LargeModelsExist.{v} :=
  largeModelsExist_of_native_largest
    (NativeSubquotient.native1242_of_nonzero_subquotient
      NativeSubquotient.TensorCoordinates.action1936 U₀ U₁ E hE hEA hEB P hP hPA hPB)
    (NativeSubquotient.native1792_of_nonzero_quotient
      NativeSubquotient.TensorCoordinates.action2420 Q hQ hQA hQB)

/-- The saved source embedding has checked rank, and the saved 1792 map has
checked native tensor coordinates and a nonzero entry. The saved 1242 quotient
is nonzero as well. Source/quotient intertwining remains. This assembly does
not assert `LargeModelsExist` until all six generator equations are supplied. -/
theorem largeModelsExist_of_saved_source
    (U₀ U₁ : Matrix (Fin 1474) (Fin 1474) (ZMod 2))
    (hEA : (NativeSubquotient.TensorCoordinates.action1936 Degree220Pair.generatorA).comp
      (Matrix.toLin' NativeSubquotient.Subquotient1242.embedding) =
      (Matrix.toLin' NativeSubquotient.Subquotient1242.embedding).comp (Matrix.toLin' U₀))
    (hEB : (NativeSubquotient.TensorCoordinates.action1936 Degree220Pair.generatorB).comp
      (Matrix.toLin' NativeSubquotient.Subquotient1242.embedding) =
      (Matrix.toLin' NativeSubquotient.Subquotient1242.embedding).comp (Matrix.toLin' U₁))
    (hPA : NativeSubquotient.Subquotient1242.projection * U₀ =
      Data1242.first.transpose * NativeSubquotient.Subquotient1242.projection)
    (hPB : NativeSubquotient.Subquotient1242.projection * U₁ =
      Data1242.second.transpose * NativeSubquotient.Subquotient1242.projection)
    (hQA : Degree220Pair.NativeActions.CertificatePacked.matrix 2420 2420
      NativeSubquotient.Largest1792.ambientA * NativeSubquotient.Largest1792.embedding =
      NativeSubquotient.Largest1792.embedding *
        Degree220Pair.NativeActions.CertificatePacked.matrix 1792 1792
          NativeSubquotient.Largest1792.targetA)
    (hQB : Degree220Pair.NativeActions.CertificatePacked.matrix 2420 2420
      NativeSubquotient.Largest1792.ambientB * NativeSubquotient.Largest1792.embedding =
      NativeSubquotient.Largest1792.embedding *
        Degree220Pair.NativeActions.CertificatePacked.matrix 1792 1792
          NativeSubquotient.Largest1792.targetB) : LargeModelsExist.{v} := by
  apply largeModelsExist_of_native_largest
  · exact NativeSubquotient.native1242_of_nonzero_subquotient
      NativeSubquotient.TensorCoordinates.action1936 U₀ U₁
      (Matrix.toLin' NativeSubquotient.Subquotient1242.embedding)
      NativeSubquotient.Subquotient1242.embedding_injective hEA hEB
      NativeSubquotient.Subquotient1242.projection
      NativeSubquotient.Subquotient1242.projection_ne_zero hPA hPB
  · apply NativeSubquotient.Largest1792.nativeRealization_of_matrix_identities
    · simpa only [NativeSubquotient.Largest1792.target_matrix_A] using hQA
    · simpa only [NativeSubquotient.Largest1792.target_matrix_B] using hQB

/-- All eight larger absolute simple modules, on native M24, in every
coefficient universe. Every construction premise is discharged. -/
theorem largeModelsExist : LargeModelsExist.{v} :=
  largeModelsExist_of_native_largest
    NativeSubquotient.Subquotient1242.nativeRealization
    NativeSubquotient.Largest1792.nativeRealization

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels

