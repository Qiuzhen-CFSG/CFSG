module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpConstrained
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpReeCentered
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary
-- Internal continuation of the same chosen-module proof, sharing its residual data.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary

/-!
# Normalized unitary and Suzuki odd-local control

The completed reciprocal escape and the ordinary/constrained component
exclusions prove uniqueness for the original odd fixed residual in both
families. Remark 4.4.2 and the completed parabolic contradictions then give
normalizer control for every nontrivial odd actor. The same control proves
Hall faithfulness on the actual quotient L/O2(L), and supplies the literal
E.6.27 centralizer applications on the unchanged chosen orbit and Sylow.

Source: Aschbacher--Smith 4.4.3, 4.4.6(2), 4.4.14 and E.6.27,
printed pp.619--625,257; applications 7.3.4 and 7.4.1, pp.699--700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape Chapter7.NormalizedSource
open ChapterB ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_suzuki_pushingUp_no_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {a : ℕ} (ha : 1 ≤ a)
    (es : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup a)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨hn,hcore,hfix,⟨e⟩⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  rcases hw with ⟨_,_,_,_,_,_,hc,_,_,hcomm,_,_⟩
  exact no_ordinary_normalized_rankOne hc hn hcore (hV ▸ D.ne_bot) hcomm hfix
    (D.sourceOrbit_suzuki_twoRank_ge_twelve hs ha es)
    (Group.IsPerfect.not_isSolvable _) (suzuki_not_two_exponent ha es) π hπ K hK

theorem sourceOrbit_suzuki_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,W,hw,hescape⟩ := D.sourceOrbit_suzuki_reciprocal_escape
    h hmany hV hs hnm hnon hm e A hne hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have hescape' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hf => hescape (hf.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape hescape'
  rcases hcases with hordinary | hconstrained
  · exact D.sourceOrbit_suzuki_pushingUp_no_ordinary h hmany hV hs hnon hm e hw K hordinary
  · exact D.sourceOrbit_suzuki_pushingUp_no_constrained h hmany hV hnon hm e hw
      K hK hq hout hconstrained

theorem sourceOrbit_unitary_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card X)) : normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  apply D.sourceOrbit_unitary_odd_control_of_residual_uniqueness h hV hs hs2 hq ?_ X hne hX ho
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_unitary_residual_uniqueness h hmany hV hs hnm hnon hs2 hq A hn hA hodd

theorem sourceOrbit_unitary_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup ChapterE.Section06.FixedPointBounds.ParabolicCartan.oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  apply D.sourceOrbit_unitary_hall_faithful_of_residual_uniqueness h hmany hV hs hnon hs2 hq ?_ hH hlarge B hBM hHall
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_unitary_residual_uniqueness h hmany hV hs hnm hnon hs2 hq A hn hA hodd

theorem sourceOrbit_suzuki_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card X)) : normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  apply D.sourceOrbit_suzuki_odd_control_of_residual_uniqueness h hV hs hm e ?_ X hne hX ho
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_suzuki_residual_uniqueness h hmany hV hs hnm hnon hm e A hn hA hodd

theorem sourceOrbit_suzuki_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup ChapterE.Section06.FixedPointBounds.ParabolicCartan.oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  apply D.sourceOrbit_suzuki_hall_faithful_of_residual_uniqueness h hmany hV hs hnon hm e ?_ hH hlarge B hBM hHall
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_suzuki_residual_uniqueness h hmany hV hs hnm hnon hm e A hn hA hodd

/-- The literal E.6.27 application on the original chosen orbit. -/
theorem sourceOrbit_unitary_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (j : ℕ∞) < ChapterE.globalR D.sourceOrbit)
    (hn : nPrime (ChapterE.inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) j ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  apply D.sourceOrbit_centralizer_le_of_abelian_odd_control h hmany hV hnon ?_ hU hUW hj1 hj hn hJ
  intro A hne hA hodd _
  exact D.sourceOrbit_unitary_odd_control h hmany hV hs hnm hnon hs2 hq A hne hA hodd

/-- The literal E.6.27 application on the original chosen orbit. -/
theorem sourceOrbit_suzuki_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (j : ℕ∞) < ChapterE.globalR D.sourceOrbit)
    (hn : nPrime (ChapterE.inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) j ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  apply D.sourceOrbit_centralizer_le_of_abelian_odd_control h hmany hV hnon ?_ hU hUW hj1 hj hn hJ
  intro A hne hA hodd _
  exact D.sourceOrbit_suzuki_odd_control h hmany hV hs hnm hnon hm e A hne hA hodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
