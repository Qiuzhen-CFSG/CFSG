module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion

/-!
# Restricted chart functionals

The 22 dual rows of the original 112-dimensional chart restrict to the
50 displayed displacement columns. Their evaluations on the zeroth columns
of the 125 restriction matrices give the second array below. Both arrays are
certified against the actual matrices by kernel reduction. Factoring the
calculation through the restricted dual rows avoids repeating the ambient
matrix product in every polynomial coefficient.

The literals are generated from `QuadraticRelations/RestrictionData.lean` and
`OrbitCover/Data.lean`; their convention and ATLAS attribution are documented
in `PolynomialCertificate/source/README.md`. No normalization or membership
hypothesis enters either identity.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.MatrixChart
open GeneratorCertificates

def restrictedChartRows : Vector ℕ 22 := ⟨#[1076985658172387, 403664596168420, 1066074697486672, 1086467673790844, 13494298673422, 388431330624666, 815385505685496, 464745018152008, 128072564937144, 972087393646446, 630922336787642, 201418574914044, 96982931573366, 949684307088898, 597825647505110, 374601153698002, 286618153275800, 1064692021309356, 842979299906460, 654357518415494, 191659845174444, 845510841669490], rfl⟩
def chartRows : Vector ℕ 22 := ⟨#[4562771746169337138969371917980532736, 25339327770792408274374305894371426550, 8652445459093337281300032395636332800, 23868624672733508970240273278063083766, 29683994725195750055786635055983974902, 136853078278382831157320542467391488, 30118901668782984503106824016274872822, 23267811528622316005081227890094244086, 1212862941523450595300544255600099328, 6141314412124946732873728877882988800, 609650410267392621547172454450855936, 24956929663603203038935906697017819382, 2824485467091858359258840844193497088, 8831007588889838789935825634657042432, 24257596525329412453324395072706576630, 24006034997392415016651009330038397430, 29156007969986169703599459579491473910, 21843326765021262565118528425833005302, 6446840639541885444452630450621644800, 2445237358372631024514727363041515776, 22623351422040810203803176929782618614, 31640013078032157022118528649558753526], rfl⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem restrictedChartRows_spec : ∀ r : Fin 22, ∀ j : Fin 50,
    bit (restrictedChartRows.get r) j.val =
      binaryColumn (dualRows.get r) ⬝ᵥ (fun i => restrictionEmbedding i j) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chartRows_spec : ∀ r : Fin 22, ∀ a : Fin 125,
    bit (chartRows.get r) a.val = ∑ j : Fin 50,
      bit (restrictedChartRows.get r) j.val * restrictionLinearBasis a j 0 := by
  decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.MatrixChart
