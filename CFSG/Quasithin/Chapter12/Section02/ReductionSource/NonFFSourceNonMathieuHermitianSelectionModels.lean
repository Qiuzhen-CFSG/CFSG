module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSourceSelection

/-!
# Hermitian selection with its concrete model premises discharged

The actual dihedral, PSL₂ and Suzuki Sylow calculations supply all three
model clauses in source selection. Thus on the original chosen orbit,
positive weak closure constructs the selected pair using only the earlier
universal E.2 source clauses. Applying the literal tensor and torus argument
forces field degree two without a selection-model assumption.

SelectionSources and the E.2.14 rank and torus clauses remain explicit
earlier-source inputs. The field-four normalizer/centralizer argument
through 8.2.13 is also still required for the full exclusion.
Source: Aschbacher–Smith, 8.2.2–4, printed pp.714–716
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Positive weak closure and the earlier source clauses now suffice for
actual selection on the original chosen orbit. All local and concrete
model inputs are proved. -/
theorem sourceOrbit_hermitian_exists_selected_of_earlier_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (earlier : SelectionSources (G := G) KnownSimple.IsKnownSimple)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S :=
  D.sourceOrbit_hermitian_exists_selected_of_positive h hmany hV hnon hs hrow
    earlier Chapter8.Section02.HermitianSource.selectionModelSources hw

open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter

/-- The literal half-field tensor is over field four, conditional only on
the earlier universal E.2 selection and E.2.14 clauses. The concrete group
models, local setup and selected pair are no longer premises. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_earlier_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionSources (G := G) KnownSimple.IsKnownSimple)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 :=
  D.sourceOrbit_hermitian_tensor_field_four_of_selection_sources h hmany hV hs hnon
    earlier Chapter8.Section02.HermitianSource.selectionModelSources eR eT
    B C eQ n hdegree hfield hmodel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
