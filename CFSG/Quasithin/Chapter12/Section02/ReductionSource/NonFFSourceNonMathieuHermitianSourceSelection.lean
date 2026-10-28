module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianLocalSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianGeometricTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWeakClosure

/-!
# Applying the Hermitian tensor to the original local selection

Tensor descent supplies the source Hermitian row and its dimension. The
original HStar subgroup then satisfies E.2.8 and characteristic two with
no local setup premise. For n > 1, the checked bound w ≥ n gives positive
weak closure, so the earlier selection clauses construct the literal pair
and the geometric torus argument excludes it.

This reduces the tensor to field four without assuming a selected pair.
The universal SelectionSources, SelectionModelSources and E.2.14 rank and
torus clauses still need source proofs. The selected field-four consumer
retains the rank-four fixed subgroup and original Sylow normality; it
does not establish r = 5 or the normalizer/centralizer argument through
8.2.13. Final source exclusion remains with this task.
Source: Aschbacher–Smith 7.5.6 and 8.2.2–5, printed pp.701,714–717
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)

open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped MatrixGroups

private theorem hermitian_row_of_tensor
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

/-- The literal tensor gives E.2.8 and characteristic two for every original
H-star subgroup, without a local-normalization or core-closedness premise. -/
theorem sourceOrbit_hermitian_tensor_hstar_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H :=
  D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs
    (D.hermitian_row_of_tensor hs B C eQ n hdegree hfield hmodel) hH

/-- Above half-degree one, positive weak closure and the proved local setup
construct the actual selected pair from the earlier universal E.2 selection
clauses. The torus argument then excludes this branch. Those earlier clauses
and E.2.14 remain explicit; no source selection theorem is asserted here. -/
theorem sourceOrbit_hermitian_tensor_excluded_of_selection_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionSources (G := G) KnownSimple.IsKnownSimple)
    (models : SelectionModelSources)
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
  have hrow := D.hermitian_row_of_tensor hs B C eQ n hdegree hfield hmodel
  obtain ⟨H,I,k,i,S,_,h28,hchar,s⟩ :=
    D.sourceOrbit_hermitian_exists_selected_of_positive h hmany hV hnon hs hrow earlier models hwpos
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_selected_excluded_geometric h hmany hV hnon eR eT
    h28 hchar s n d B eQ hfield hn

/-- With the actual selected pair inside an original H-star subgroup, the
literal tensor supplies the rank-four field-four configuration. The local
E.2.8 and characteristic-two inputs are now discharged. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup_of_hstar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    n = 1 ∧ k = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5 := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup h hmany hV hs hnon hH
    B C eQ n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_tensor_selected_fixed_subgroup_geometric h hmany hV hs hnon
    eR eT h28 hchar s B C eQ n hdegree hfield hmodel

/-- The original tensor has field degree two once the earlier universal
selection and E.2.14 clauses are supplied. No selected group, weak-closure
bound, local setup or actor-degree assumption occurs in the input. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_selection_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionSources (G := G) KnownSimple.IsKnownSimple)
    (models : SelectionModelSources)
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
    apply D.sourceOrbit_hermitian_tensor_excluded_of_selection_sources h hmany hV hs hnon
      earlier models eR eT B C eQ n hdegree hfield hmodel
    have hp := NeZero.pos n
    omega
  exact ⟨hn, by omega⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
