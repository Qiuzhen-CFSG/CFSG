module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWitnessSelection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessRanks

/-!
# Bounded geometric selection on the original Hermitian tensor

Every higher-field H-star subgroup already supplies an actual nonsymplectic
witness. The geometric constructor transports that witness, its internal
conjugator, its original Sylow intersection and its full-core quotient into
the ambient subgroup lattice. The source non-FF hypothesis and TI property
supply the literal intersection and Borel markings.

The actor corank bounds w above by the witness degree k, so the established
higher-field bound w ≥ n gives n ≤ k. The native actor-rank argument gives
k ≤ 2n in the original Hermitian automizer. Thus these are actual geometric
selections with the parameter range used in 8.2.3, without any assumption
that k divides the E-generation parameter of H. The last theorem preserves
the field-four alternative n = 1 explicitly.

The torus exclusion must still be applied on this geometric interface, and
the field-four normalizer/centralizer argument through 8.2.13 is unfinished.
No complete Hermitian source exclusion is asserted here.

Source: Aschbacher--Smith 7.5.6 and 8.2.2--4, printed pp.701,714--716,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.HermitianSource
open ChapterE.Witnesses.BenderPlacement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)

/-- Every original higher-field H-star subgroup supplies a geometric pair
with n ≤ k ≤ 2n, independently of its E-generation parameter. -/
theorem sourceOrbit_hermitian_tensor_higher_geometric_selection
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧
        1 < k ∧ n ≤ k ∧ k ≤ 2*n := by
  obtain ⟨R,hR,f,w,hk⟩ := D.sourceOrbit_hermitian_tensor_higher_original_witness
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel hn
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel
  obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) R hR w
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  obtain ⟨j,hj,_,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hl : n ≤ w.degree := ENat.natCast_le_natCast.mp
    (hw.trans (s.core_actor_data D.sourceOrbit_weakClosure_setup).2.2.2.2)
  exact ⟨I,w.degree,i,S,s,hk,hl,s.parameter_le_twice_half_degree n j hj⟩

/-- The original tensor retains field four and otherwise constructs the
bounded geometric selection on the original action and Sylow subgroup. -/
theorem sourceOrbit_hermitian_tensor_field_four_or_geometric_selection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    (n = 1 ∧ B.degree = 2) ∨
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
        GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧
          1 < k ∧ n ≤ k ∧ k ≤ 2*n := by
  by_cases hn : n = 1
  · exact Or.inl ⟨hn,by omega⟩
  have hn' : 1 < n := by have := NeZero.pos n; omega
  rcases D.sourceOrbit_hermitian_tensor_field_four_or_original_witness
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel with hf | ⟨H,hH,_⟩
  · exact (hn hf.1).elim
  · exact Or.inr ⟨H,hH,D.sourceOrbit_hermitian_tensor_higher_geometric_selection
      h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel hn'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
