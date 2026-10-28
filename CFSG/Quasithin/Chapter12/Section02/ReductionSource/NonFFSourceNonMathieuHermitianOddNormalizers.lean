module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianOuterSections
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCentralizers
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl

/-!
# Placed odd-normalizer components on the original Hermitian orbit

Above half-degree one, the marked component quotient is no section of any
Theorem B component's outer group. In the branch where the original perfect
odd fixed residual is a uniqueness subgroup, this puts that residual and the
original module in an actual normal component. Its odd centralizer preserves
the module's rank 9n >= 18. The existing rank sieve and Bender exclusion leave
only the relative-rank-two characteristic-two component models.

The final tensor application refines failure of r >= 4n to either the original
C.2.8 pushing-up configuration or this placed component. Residual uniqueness
is used only in the corresponding alternative, not assumed by the final
application. The two configuration exclusions, the separate n = 1 branch,
weak-closure bounds and terminal exclusion remain with
qt-d-1222-nonmathieu-hermitian-exclusion.

The proof-only `import all` deliberately reuses the internal chosen-module
rank and component transports from NonFFSourceRankOneOddControl. Their public
boundary is unchanged, and no unitary, Suzuki or natural-module hypothesis
is imported into the Hermitian statements.
Source: Aschbacher--Smith, 4.4.6--12 and 7.4.1, printed pp.620--622,699--700
(refs/quasithin.pdf).
-/

public noncomputable section
open scoped Classical IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]

omit [NeZero n] in
/-- Above field four, the original component quotient is no section of the
outer group of any B-model quasisimple component. -/
theorem sourceOrbit_hermitian_no_outer_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    {K : Type v} [Group K] [Finite K] [IsQuasisimple K]
    (hK : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (U : Subgroup (MulAut.Outer K))
    (f : U →* (D.orbitComponent ⧸ center D.orbitComponent)) : ¬ Function.Surjective f := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  exact Chapter7.NormalizedSource.NonMathieuHermitian.no_hermitian_outer_section hK
    (Group.IsPerfect.not_isSolvable _) eQ hn (by rw [B.card_eq,hfield]) U f

/-- The normal component contains the original module and perfect residual;
its quotient has relative Lie rank two. No outer-section premise remains. -/
theorem sourceOrbit_hermitian_rankTwo_component_of_unique
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  have hr : 12 ≤ primeRank 2 D.sourceOrbit := by
    have hb := D.sourceOrbit_rank_ge_of_finrank
      ((D.hermitianOrbitCoordinates n d).finrank_eq.trans (finrank_binary n))
    omega
  apply D.sourceOrbit_rankTwo_component_of_unique_and_no_outer_sections h hV
    (D.sourceOrbit_hermitian_card_gt_eight n d) hr A hne hA ho hu hout
  intro K hcomp hK U f
  let : IsQuasisimple K := hcomp.2
  exact D.sourceOrbit_hermitian_no_outer_section n h B eQ hfield hn hK U f

set_option maxHeartbeats 400000 in
/-- The coordinate version retains the same escaping odd actor and
replaces the unplaced component branch by the actual rank-two component. -/
theorem sourceOrbit_hermitian_refined_oddNormalizer_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (hr : globalR D.sourceOrbit < ((4*n : ℕ) : ℕ∞)) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
      Odd (Nat.card A) ∧ IsMulCommutative A ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (L : Set G) ∧
      (PushingUpCase L D.sourceOrbit A ∨
        RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent)) := by
  obtain ⟨A,hne,hA,ho,ha,hout,hcore,hcases⟩ :=
    D.sourceOrbit_hermitian_oddNormalizer_obstruction n d h hmany hV hnon hr
  let := ha
  refine ⟨A,hne,hA,ho,ha,hout,hcore,?_⟩
  rcases hcases with hpush | hcomp
  · exact Or.inl hpush
  · exact Or.inr (D.sourceOrbit_hermitian_rankTwo_component_of_unique n h.toHypothesis1221 hV
      d B eQ hfield hn A hne hA ho hcomp.1 hout)

set_option maxHeartbeats 400000 in
/-- The literal half-field tensor reduces failure of r >= 4n, for n > 1,
to the actual C.2.8 configuration or a placed relative-rank-two component.
All odd-element, higher Thompson, odd-core and outer-section inputs are proved. -/
theorem sourceOrbit_hermitian_tensor_refined_oddNormalizer_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) (hr : globalR D.sourceOrbit < ((4*n : ℕ) : ℕ∞)) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
      Odd (Nat.card A) ∧ IsMulCommutative A ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (L : Set G) ∧
      (PushingUpCase L D.sourceOrbit A ∨
        RankTwoComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent)) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_refined_oddNormalizer_obstruction n h hmany hV hnon
    d B eQ hfield hn hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
