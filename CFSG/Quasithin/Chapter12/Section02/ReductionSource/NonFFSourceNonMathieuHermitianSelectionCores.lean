module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCores
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSourceSelection

/-!
# Applying the reduced selection clauses to the original Hermitian tensor

The actual two-conjugate pair inherits characteristic two, its classified
nonsymplectic normal core is its two-core, and its Borel image normalizes the
specified quotient Sylow. Thus the original chosen-orbit selection no longer
needs the separate E.2.9(2), E.2.11(3), or E.2.11(5) inputs. Concrete model
normalizers and ranks are also supplied by proved theorems.

For half-degree greater than one, the original weak-closure bound gives
positive weak closure, and this selection feeds the geometric torus exclusion.
The tensor therefore reduces to field four conditional on the remaining
selection clauses and E.2.14 rank and torus clauses. Those clauses, selection
at half-degree one, and the field-four normalizer/centralizer argument through
8.2.13 remain to be discharged; this module does not assert the full exclusion.

Source: Aschbacher–Smith, E.2.9–14 and 8.2.2–5, printed pp.221–228,714–717
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal chosen orbit supplies all local setup, core and model
clauses; only the four remaining selection clauses and positive weak closure
are explicit. The original Sylow and conjugator are preserved. -/
theorem sourceOrbit_hermitian_exists_selected_of_remaining_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (earlier : SelectionRemainingSources (G := G) KnownSimple.IsKnownSimple)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S := by
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨I,k,i,S,s⟩ := exists_selected_of_remaining_sources earlier h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) hw
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  exact ⟨H,I,k,i,S,hH,h28,hchar,s⟩

open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped MatrixGroups

private theorem hermitian_row_for_core_selection
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  refine ⟨B,C,⟨eQ⟩,?_⟩
  dsimp only
  rw [hdegree]
  exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩

/-- Above half-degree one, positive weak closure and the reduced selection
clauses construct the actual pair. The geometric torus argument excludes
this branch; the four remaining selection clauses and E.2.14 rank and torus
clauses are still explicit. -/
theorem sourceOrbit_hermitian_tensor_excluded_of_remaining_selection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionRemainingSources (G := G) KnownSimple.IsKnownSimple)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) : False := by
  have hw := D.sourceOrbit_hermitian_tensor_globalW_ge n h hmany hV hs hnon
    B C eQ hdegree hfield hmodel hn
  have hwpos : 0 < globalW D.sourceOrbit T :=
    (show (0 : ℕ∞) < (n : ℕ∞) by exact_mod_cast NeZero.pos n).trans_le hw
  have hrow := D.hermitian_row_for_core_selection hs B C eQ n hdegree hfield hmodel
  obtain ⟨H,I,k,i,S,_,h28,hchar,s⟩ :=
    D.sourceOrbit_hermitian_exists_selected_of_remaining_sources h hmany hV hnon hs hrow earlier hwpos
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_selected_excluded_geometric h hmany hV hnon eR eT
    h28 hchar s n d B eQ hfield hn

/-- The original tensor has field degree two from the four remaining
selection clauses and E.2.14 rank and torus clauses. The selected pair and
positive weak closure in the higher-degree branch are constructed internally. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_remaining_selection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionRemainingSources (G := G) KnownSimple.IsKnownSimple)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    : n = 1 ∧ B.degree = 2 := by
  have hn : n = 1 := by
    by_contra hn
    apply D.sourceOrbit_hermitian_tensor_excluded_of_remaining_selection h hmany hV hs hnon
      earlier eR eT B C eQ n hdegree hfield hmodel
    have hp := NeZero.pos n
    omega
  exact ⟨hn, by omega⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
