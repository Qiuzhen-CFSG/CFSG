module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.DensityCriterion

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.LeftInverseA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.RightInverseA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.LeftOrbitA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.RightOrbitA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.LeftInverseB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.RightInverseB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.LeftOrbitB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.RightOrbitB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeAA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeBA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposePA

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeAB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeBB

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposePB

/-!
# Both degree-320 orbit bases span

The literal stored columns and rows are generator-word translates of the
recorded column and covector. Bounded kernel certificates check every prefix
step, all needed transposes, and both specified one-sided inverse products.
The left words are interpreted in column order; right words retain row order.

The conditional applications discharge the orbit-spanning premise of the
rank-one density criterion and its native absolute-irreducibility consumer.
Rank-one membership and realization of the native action remain explicit.
Source data and attribution: `source/README.md`; certificate measurements:
`OrbitSpanning/source/README.md`.
-/

public noncomputable section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels

open OrbitCertificates

private theorem word_mem (variant : Bool) (w : List Bool) :
    OneSixty.wordValue (matrixA variant) (matrixB variant) w ∈ generated variant := by
  apply OneSixty.wordValue_mem
  · exact Algebra.subset_adjoin (Set.mem_insert _ _)
  · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem leftA (i : Fin 320) : ∃ W ∈ generated false,
    W.mulVec (column false) = fun k => leftBasis false k i := by
  refine ⟨OneSixty.wordValue (matrixA false) (matrixB false) (Data.leftAWords[i.val]!.reverse),
    word_mem false _, ?_⟩
  exact column_orbit 320 Degree320Pair.Data.Aa Degree320Pair.Data.Ba Data.AATranspose Data.BATranspose WitnessData.PA Data.leftAColumns WitnessData.columnA
    Data.leftAParents Data.leftALetters Data.leftAWords
    TransposeAA.check TransposeBA.check TransposePA.check LeftOrbitA.check i

private theorem rightA (i : Fin 320) : ∃ W ∈ generated false,
    Matrix.vecMul (covector false) W = rightBasis false i := by
  refine ⟨OneSixty.wordValue (matrixA false) (matrixB false) (Data.rightAWords[i.val]!),
    word_mem false _, ?_⟩
  exact row_orbit 320 Degree320Pair.Data.Aa Degree320Pair.Data.Ba WitnessData.covectorA WitnessData.QA
    Data.rightAParents Data.rightALetters Data.rightAWords RightOrbitA.check i

private theorem leftB (i : Fin 320) : ∃ W ∈ generated true,
    W.mulVec (column true) = fun k => leftBasis true k i := by
  refine ⟨OneSixty.wordValue (matrixA true) (matrixB true) (Data.leftBWords[i.val]!.reverse),
    word_mem true _, ?_⟩
  exact column_orbit 320 Degree320Pair.Data.Ab Degree320Pair.Data.Bb Data.ABTranspose Data.BBTranspose WitnessData.PB Data.leftBColumns WitnessData.columnB
    Data.leftBParents Data.leftBLetters Data.leftBWords
    TransposeAB.check TransposeBB.check TransposePB.check LeftOrbitB.check i

private theorem rightB (i : Fin 320) : ∃ W ∈ generated true,
    Matrix.vecMul (covector true) W = rightBasis true i := by
  refine ⟨OneSixty.wordValue (matrixA true) (matrixB true) (Data.rightBWords[i.val]!),
    word_mem true _, ?_⟩
  exact row_orbit 320 Degree320Pair.Data.Ab Degree320Pair.Data.Bb WitnessData.covectorB WitnessData.QB
    Data.rightBParents Data.rightBLetters Data.rightBWords RightOrbitB.check i

/-- Both literal stored bases are generated translates and have the specified
one-sided inverses. No rank-one or native-action premise is used. -/
theorem orbitSpanning : OrbitSpanning := by
  intro variant
  cases variant
  · exact ⟨leftA, rightA, LeftInverseA.identity, RightInverseA.identity⟩
  · exact ⟨leftB, rightB, LeftInverseB.identity, RightInverseB.identity⟩

/-- The orbit certificates discharge the spanning premise of matrix density. -/
theorem generatorDensity_of_membership (hr : RankOneMembership) : GeneratorDensity :=
  generatorDensity_of_rankOne hr orbitSpanning

/-- Native consumer, with precisely rank-one membership and marking retained. -/
theorem absolute_of_membership (hr : RankOneMembership) (variant : Bool)
    (ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes variant ρ) : ρ.IsAbsolutelyIrreducible :=
  absolute_of_rankOne hr orbitSpanning variant ρ hρ

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
