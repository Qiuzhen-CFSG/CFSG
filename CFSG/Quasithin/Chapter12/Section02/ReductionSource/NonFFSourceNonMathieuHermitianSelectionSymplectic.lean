module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionSymplectic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianLinearTorus

/-!
# Hermitian selection without the symplectic source premise

The original TI condition and non-FF bound identify the family normalizer.
Positive weak closure then excludes its actual symplectic quotient using
the two-conjugate core and the two parabolic radicals. This supplies the
missing symplectic clause on the original orbit, Sylow and conjugator.

The literal half-field tensor consequently reduces to field four or an
actual selected Suzuki quotient, with only family existence left as a
selection input. No E.2.13(6) callback or E.2.14 rank or linear-torus clause
is assumed. The Suzuki torus clause and the field-four normalizer/centralizer
argument through 8.2.13 remain unfinished.

Source: Aschbacher–Smith E.2.13(6), p.225, and 8.2.2–5, pp.714–717
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Selection on the literal chosen-orbit family, with symplectic exclusion
derived from the original positive weak-closure hypothesis. -/
theorem sourceOrbit_hermitian_selected_of_family
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    {H I : Subgroup G} {k : ℕ}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (f : Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  exact exists_selected_of_family h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) f hw
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)

/-- Only existence of the source family remains in selection; the callback
is restricted to the actual chosen orbit and original Sylow. -/
theorem sourceOrbit_hermitian_exists_selected_of_family_existence
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (earlier : ∀ H : Subgroup G,
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit →
        ∃ I k, Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S := by
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨I,k,f⟩ := earlier H h28
  obtain ⟨i,S,s⟩ := D.sourceOrbit_hermitian_selected_of_family h hmany hV hnon hs hrow hH f hw
  exact ⟨H,I,k,i,S,hH,s⟩

open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups

/-- The actual tensor reduces to field four or a selected Suzuki quotient
assuming only the remaining source-family existence input. Symplectic
exclusion, center marking, actor rank and the linear torus are discharged.
Half-degree one is retained in the field-four alternative. -/
theorem sourceOrbit_hermitian_tensor_field_four_or_suzuki_of_family_existence
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : ∀ H : Subgroup G,
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit →
        ∃ I k, Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    (n = 1 ∧ B.degree = 2) ∨
      ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I) (m : ℕ),
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧
        1 < n ∧ 0 < m ∧ k = 2*m+1 ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m) := by
  by_cases hn : n = 1
  · exact Or.inl ⟨hn,by omega⟩
  have hn' : 1 < n := by have hp := NeZero.pos n; omega
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hw := D.sourceOrbit_hermitian_tensor_globalW_ge n h hmany hV hs hnon
    B C eQ hdegree hfield hmodel hn'
  have hwpos : 0 < globalW D.sourceOrbit T :=
    (show (0 : ℕ∞) < (n : ℕ∞) by exact_mod_cast NeZero.pos n).trans_le hw
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,I,k,i,S,hH,s⟩ :=
    D.sourceOrbit_hermitian_exists_selected_of_family_existence h hmany hV hnon hs hrow earlier hwpos
  rcases D.sourceOrbit_hermitian_selected_suzuki_or_field_four h hmany hV hnon s n d B eQ hfield with
    ⟨he,_,_⟩ | ⟨hn,m,hm,hk,he⟩
  · exact (hn he).elim
  · exact Or.inr ⟨H,I,k,i,S,m,hH,s,hn,hm,hk,he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
