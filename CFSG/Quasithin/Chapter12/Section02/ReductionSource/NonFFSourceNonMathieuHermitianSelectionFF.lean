module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionFF
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectionCores

/-!
# Removing the zero-intersection premise on the chosen Hermitian orbit

The E.2.13(5) proof uses the actual family quotient and embeds its actor in
Aut_H(V). Non-FF for the original orbit therefore forces a nontrivial
intersection for every family witness, including half-degree one.

The original selection and tensor consumers consequently no longer assume
that FF clause. Witness existence, symplectic exclusion, and the center
marking remain explicit; so do E.2.14's rank and torus clauses. These
conditional reductions do not finish the Hermitian exclusion or its
field-four normalizer/centralizer argument through 8.2.13.

Source: Aschbacher–Smith, E.2.13(5), printed pp.224–225, and 8.2.2–5,
printed pp.714–717 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H I : Subgroup G}
  (D : ChosenModule T L V)

/-- Every actual family witness has nontrivial intersection on the original
chosen orbit. No selection-source premise is used in this implication. -/
theorem sourceOrbit_hermitian_family_intersection_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {k : ℕ} (f : Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (i : I)
    (hgen : D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom = I) :
    D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥ := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  exact family_intersection_ne_bot_of_quadraticRatio_gt_one h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) f i hgen
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon H)

/-- The actual chosen-orbit selection with only the three remaining
structural source clauses and positive weak closure explicit. -/
theorem sourceOrbit_hermitian_exists_selected_of_structural_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (earlier : SelectionStructuralSources (G := G) KnownSimple.IsKnownSimple)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S :=
  D.sourceOrbit_hermitian_exists_selected_of_remaining_sources h hmany hV hnon hs hrow
    earlier.remaining hw
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped MatrixGroups

/-- The literal half-field tensor supplies the family-intersection
conclusion also at half-degree one; the original action and Sylow remain fixed. -/
theorem sourceOrbit_hermitian_tensor_family_intersection_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {k : ℕ} (f : Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (i : I)
    (hgen : D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    : D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥ := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel
  exact family_intersection_ne_bot_of_quadraticRatio_gt_one h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) f i hgen
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon H)

/-- The literal tensor reduces to field four conditional on the three
remaining selection clauses and E.2.14's rank and torus clauses. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_structural_selection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionStructuralSources (G := G) KnownSimple.IsKnownSimple)
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
    : n = 1 ∧ B.degree = 2 :=
  D.sourceOrbit_hermitian_tensor_field_four_of_remaining_selection h hmany hV hs hnon
    earlier.remaining eR eT B C eQ n hdegree hfield hmodel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
