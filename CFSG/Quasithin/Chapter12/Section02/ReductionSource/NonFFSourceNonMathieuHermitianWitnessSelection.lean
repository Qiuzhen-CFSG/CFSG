module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianDihedralSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWeakClosure

/-!
# Original witness construction on the chosen Hermitian tensor

The proved H-star normalization and higher-field weak-closure bound discharge
all premises of the original witness constructor. Thus every actual H-star
subgroup supplies a nonsymplectic pair with the original orbit, internal
conjugator, Sylow intersection and full-core quotient markings. Degree one
would give the already checked selected dihedral pair and force n = 1, so
these higher-field witnesses have degree greater than one.

The second theorem retains n = 1 explicitly: every positive half-field tensor
has field four or supplies such an actual witness on an actual H-star group.
The witness degree is not yet linked to generationParameter H; conversion to
the existing selected-family interface and the normalizer/centralizer argument
through 8.2.13 remain with the Hermitian exclusion assembly. This module does
not assert the full exclusion.

Source: Aschbacher--Smith E.2.7--9, E.2.13(6), 7.5.6 and 8.2.2--4,
printed pp.218--225,714--716, refs/quasithin.pdf (1 March 2004 manuscript).
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

/-- The actual higher-field Hermitian tensor constructs its nonsymplectic
source witness inside each original H-star subgroup. The witness has degree
greater than one, since degree one forces field four on the same action. -/
theorem sourceOrbit_hermitian_tensor_higher_original_witness
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
    ∃ R : Sylow 2 H, (R : Subgroup H) = (T : Subgroup G).subgroupOf H ∧
      ∃ f : ℕ, ∃ w : OriginalWitness R ((normalizer (L : Set G)).subgroupOf H)
        (D.sourceOrbit.subgroupOf H) f, 1 < w.degree := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hpos : 0 < globalW D.sourceOrbit T :=
    lt_of_lt_of_le (by exact_mod_cast (NeZero.pos n)) hw
  obtain ⟨R,hR,f,⟨w⟩⟩ := exists_original_witness_of_positive_weak_closure h28 hfit
    (D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH) hpos
  refine ⟨R,hR,f,w,?_⟩
  by_contra! hsmall
  have hd : w.degree = 1 := by have := w.positive; omega
  obtain ⟨I,i,S,s⟩ := selected_one_of_original_witness h28 hfit R hR w hd
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hn' := (selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
    n (D.hermitianOrbitCoordinates n d) j hj he).1
  omega

/-- Without dropping n = 1, the literal tensor either has field four or
constructs a genuine nonsymplectic pair on an actual H-star subgroup. -/
theorem sourceOrbit_hermitian_tensor_field_four_or_original_witness
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
      ∃ R : Sylow 2 H, (R : Subgroup H) = (T : Subgroup G).subgroupOf H ∧
      ∃ f : ℕ, ∃ w : OriginalWitness R ((normalizer (L : Set G)).subgroupOf H)
        (D.sourceOrbit.subgroupOf H) f, 1 < w.degree := by
  by_cases hn : n = 1
  · exact Or.inl ⟨hn,by omega⟩
  have hn' : 1 < n := by have := NeZero.pos n; omega
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  exact Or.inr ⟨H,hH,D.sourceOrbit_hermitian_tensor_higher_original_witness
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel hn'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
