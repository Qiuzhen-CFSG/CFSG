module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianInitialBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl

/-!
# Actual odd-normalizer obstructions for the Hermitian chosen orbit

The original small-subspace centralizer has a two-group action image, odd
Cartan parameter one, and the required higher Thompson containment. E.6.27
therefore gives the improved r-bound conditional only on ambient odd-normalizer
control. Independently, the literal module has order 2^(9n) > 8, so 4.4.8
places the odd core of each relevant odd normalizer in N_G(L).

If the r-bound fails, an actual nontrivial abelian odd subgroup has a normalizer
escaping N_G(L). It produces either the complete C.2.8 pushing-up configuration
or a component moved by the original module, with its actual Theorem B model.
Tensor descent supplies the literal coordinate marking, including n = 1.
These are reductions, not ambient normalizer control or the final exclusion.
Both configuration exclusions and final assembly remain with
qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith, 4.4.2--11 and 7.4.1, printed pp.619--621,699--700
(refs/quasithin.pdf).
-/

public noncomputable section
open scoped Classical IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

include d in
/-- The two local hypotheses of E.6.27 on the original small-subspace
centralizer, together with its stronger two-group action-image conclusion. -/
theorem sourceOrbit_hermitian_smallCentralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ D.sourceOrbit)
    (hc : subgroupCorank D.sourceOrbit U < 4*n) :
    let X := normalizer (L : Set G) ⊓ centralizer (U : Set G)
    IsPGroup 2 (inducedAutomizer D.sourceOrbit X) ∧
      nPrime (inducedAutomizer D.sourceOrbit X) = 1 ∧
      thompsonJ X 1 ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hE := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  have hXN := hE.localCentralizer_le_normalizer hU hUV
  exact ⟨Chapter8.Section02.HermitianSource.localCentralizer_image_isTwo D.sourceOrbit _ n
      (D.hermitianOrbitCoordinates n d) j hj he hXN hUV inf_le_right hc,
    Chapter8.Section02.HermitianSource.localCentralizer_nPrime_eq_one D.sourceOrbit _ n
      (D.hermitianOrbitCoordinates n d) j hj he hXN hUV inf_le_right hc,
    Chapter8.Section02.HermitianSource.localCentralizer_thompson_one D.sourceOrbit n
      (D.hermitianOrbitCoordinates n d) j hj he hE hU hUV hc⟩

include d in
/-- The original r-bound after ambient odd-normalizer control; its local
representation and Thompson premises have all been discharged. -/
theorem sourceOrbit_hermitian_globalR_ge_four_mul_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcontrol : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
        normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hr := (D.sourceOrbit_hermitian_initial_parameters n d h hmany hV hnon).1
  have hpos : (1 : ℕ∞) < ((3*n : ℕ) : ℕ∞) := by
    exact_mod_cast (show 1 < 3*n by have := NeZero.pos n; omega)
  exact Chapter8.Section02.HermitianSource.globalR_ge_four_mul_of_odd_control D.sourceOrbit n
    (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon)
    (hpos.trans_le hr) hcontrol

include d in
theorem sourceOrbit_hermitian_card_gt_eight : 8 < Nat.card D.sourceOrbit := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  change Nat.card D.sourceOrbit = _ at hc
  rw [Nat.card_zmod,(D.hermitianOrbitCoordinates n d).finrank_eq,finrank_binary] at hc
  rw [hc]
  have hn : 3 < 9*n := by have := NeZero.pos n; omega
  exact (show 8 = 2^3 by norm_num).trans_lt (Nat.pow_lt_pow_right (by decide) hn)

include d in
/-- The odd core of every relevant ambient odd normalizer already lies in M.
This uses the literal 9n-dimensional module, including half-degree one. -/
theorem sourceOrbit_hermitian_oddNormalizer_oddCore
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    let O := (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype
    ⁅D.sourceOrbit,O⁆ = ⊥ ∧ O ≤ normalizer (L : Set G) := by
  have hs := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hc : ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ := by
    simpa only [hV] using chosen_oddNormalizer_centralizes_oddCore_of_large_module h D
      (show 8 < Nat.card V from hV ▸ D.sourceOrbit_hermitian_card_gt_eight n d)
      A hs.1 hs.2 ho (show A ≤ centralizer (V : Set G) from hV ▸ hA.trans inf_le_right)
  exact ⟨hc,(le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans (D.sourceOrbit_normalizer_le h))⟩

include d in
/-- A failure of r >= 4n yields an actual escaping odd normalizer and one
of its two source configurations, with the original residual and module. -/
theorem sourceOrbit_hermitian_oddNormalizer_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hr : globalR D.sourceOrbit < ((4*n : ℕ) : ℕ∞)) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
      Odd (Nat.card A) ∧ IsMulCommutative A ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (L : Set G) ∧
      (PushingUpCase L D.sourceOrbit A ∨ ComponentCase L D.sourceOrbit A) := by
  have hf : ¬ ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
        normalizer (A : Set G) ≤ normalizer (L : Set G) := by
    intro hc
    exact (not_le_of_gt hr)
      (D.sourceOrbit_hermitian_globalR_ge_four_mul_of_odd_control n d h hmany hV hnon hc)
  push Not at hf
  obtain ⟨A,hne,hA,ho,ha,hout⟩ := hf
  let := ha
  have hcore := (D.sourceOrbit_hermitian_oddNormalizer_oddCore n d h.toHypothesis1221 hV A hA ho).2
  refine ⟨A,hne,hA,ho,ha,hout,hcore,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · apply Or.inr
    refine ⟨hu,?_⟩
    have hs := (le_sectionCentralizer_iff A L).mp
      (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
    simpa only [hV] using component_of_unique h.toHypothesis1221 D
      (show 8 < Nat.card V from hV ▸ D.sourceOrbit_hermitian_card_gt_eight n d)
      A hne hs.1 hs.2 ho (show A ≤ centralizer (V : Set G) from hV ▸ hA.trans inf_le_right)
      hu hout
  · exact Or.inl (D.sourceOrbit_pushingUp_case_of_not_unique h.toHypothesis1221 hV A hA ho hu)

/-- Literal tensor application of the ambient obstruction. No normalizer,
selection, rank or source-configuration output is assumed. -/
theorem sourceOrbit_hermitian_tensor_oddNormalizer_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hr : globalR D.sourceOrbit < ((4*n : ℕ) : ℕ∞)) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
      Odd (Nat.card A) ∧ IsMulCommutative A ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (L : Set G) ∧
      (PushingUpCase L D.sourceOrbit A ∨ ComponentCase L D.sourceOrbit A) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_oddNormalizer_obstruction n d h hmany hV hnon hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
