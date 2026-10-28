module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Trace
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions
public import Mathlib.RepresentationTheory.Character

/-!
# Two inequivalent absolutely irreducible binary degree-220 M24 modules

The ATLAS pairs have different traces at the product of their marked
standard generators. Any native realizations are therefore inequivalent.
Full generation of the explicit matrix algebras implies absolute
irreducibility, by density and scalar extension.

The native realizations come from a quotient of the fifth exterior power of
the Golay code module and its contragredient, with both marked generator
matrices checked. Independent rank-one and orbit certificates establish
full matrix-algebra generation. `pair220` combines these constructions with
trace separation, discharging both inputs of the conditional assembly.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1,
manuscript p.17; ATLAS data and conventions in `Degree220Pair/Data.lean`.
-/

@[expose] public noncomputable section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
open Sporadic.Mathieu

/-- The literal generator matrices transfer the full algebra to the native action. -/
theorem action_dense_of_realizes (second : Bool)
    (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2)) (hρ : Realizes second ρ)
    (hd : Algebra.adjoin (ZMod 2) ({matrixA second, matrixB second} :
      Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) = ⊤) :
    Algebra.adjoin (ZMod 2) (Set.range ρ) = ⊤ := by
  let S := Algebra.adjoin (ZMod 2) (Set.range ρ)
  have hle : Algebra.adjoin (ZMod 2) ({matrixA second, matrixB second} :
      Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) ≤
      S.comap Matrix.toLinAlgEquiv'.toAlgHom := by
    apply Algebra.adjoin_le
    intro M hM
    rcases hM with rfl | hM
    · change Matrix.toLin' (matrixA second) ∈ S
      rw [← hρ.1, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self generatorA)
    · have hM' : M = matrixB second := hM
      subst M
      change Matrix.toLin' (matrixB second) ∈ S
      rw [← hρ.2, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self generatorB)
  apply top_unique
  intro f _
  have hm : LinearMap.toMatrix' f ∈ Algebra.adjoin (ZMod 2)
      ({matrixA second, matrixB second} : Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) := by
    rw [hd]
    trivial
  have hf := hle hm
  change Matrix.toLin' (LinearMap.toMatrix' f) ∈ S at hf
  simpa only [Matrix.toLin'_toMatrix'] using hf

/-- Full matrix generation implies genuine absolute irreducibility. -/
theorem absolute_of_realizes (second : Bool)
    (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2)) (hρ : Realizes second ρ)
    (hd : Algebra.adjoin (ZMod 2) ({matrixA second, matrixB second} :
      Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) = ⊤) :
    ρ.IsAbsolutelyIrreducible := by
  let : ρ.IsIrreducible :=
    irreducible_of_jacobson_density_surjective ρ (action_dense_of_realizes second ρ hρ hd)
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  exact surjective_of_jacobson_density_surjective_rep ρ
    (action_dense_of_realizes second ρ hρ hd)

/-- Evaluate the trace on the same marked native word for either realization. -/
theorem character_product_of_realizes (second : Bool)
    (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2)) (hρ : Realizes second ρ) :
    ρ.character (generatorA * generatorB) = Matrix.trace (matrixA second * matrixB second) := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 220))]
  change (LinearMap.toMatrix' (ρ (generatorA * generatorB))).trace = _
  rw [map_mul, LinearMap.toMatrix'_mul, hρ.1, hρ.2]

/-- The checked binary traces distinguish any two marked native realizations. -/
theorem inequivalent_of_realizes
    (ρ σ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2))
    (hρ : Realizes false ρ) (hσ : Realizes true σ) : IsEmpty (ρ.Equiv σ) := by
  constructor
  intro e
  have h := congrFun (Representation.char_iso e) (generatorA * generatorB)
  rw [character_product_of_realizes false ρ hρ, character_product_of_realizes true σ hσ,
    trace_first, trace_second] at h
  exact one_ne_zero h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels

/-- Discharge the degree-220 pair input of `largeModelsExist_of_candidates`
from the native realization and the independent finite algebra certificates. -/
theorem pair220_of_nativeRealizations_of_matrixAlgebrasFull
    (hn : Degree220Pair.NativeRealizationsExist) (hd : Degree220Pair.MatrixAlgebrasFull) :
    Nonempty (BinaryPair 220) := by
  obtain ⟨ρ, hρ⟩ := hn
  exact ⟨{
    first := ⟨ρ false, Degree220Pair.absolute_of_realizes false (ρ false) (hρ false) (hd false)⟩
    second := ⟨ρ true, Degree220Pair.absolute_of_realizes true (ρ true) (hρ true) (hd true)⟩
    inequivalent := Degree220Pair.inequivalent_of_realizes (ρ false) (ρ true) (hρ false) (hρ true)
  }⟩

/-- Two inequivalent absolutely irreducible degree-220 representations over
the binary field, acting on the full native Witt-design M24. -/
theorem pair220 : Nonempty (BinaryPair 220) :=
  pair220_of_nativeRealizations_of_matrixAlgebrasFull
    Degree220Pair.nativeRealizationsExist Degree220Pair.matrixAlgebrasFull

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
