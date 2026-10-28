module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianParabolics
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianOddNormalizers

/-!
# Eliminating the placed component on the original Hermitian chosen orbit

The odd fixed residual covers the original L and maps onto the central
quotient of the original orbit component. The original chosen module is
its nontrivial commutator module inside its two-core. Thus the square-field
PSL₃ parabolic exclusion applies to the actual inclusion and quotient maps.

Consequently residual uniqueness implies ambient odd-normalizer control for
n > 1. The literal tensor application reduces r < 4n to the pushing-up
configuration alone. The component exclusion includes n = 1, while the
available component-selection theorem still requires n > 1.

The pushing-up exclusion, n = 1 selection, weak-closure bounds and terminal
Hermitian exclusion remain with qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith 4.4.11--12 and 7.4.1, pp.621--622,699--700
(refs/quasithin.pdf).
-/

public noncomputable section
open scoped Classical IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual fixed residual and chosen orbit rule out every placed rank-two component. -/
theorem sourceOrbit_hermitian_no_rankTwo_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    {n : ℕ} (hfield : B.degree = 2*n)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ¬ RankTwoComponentCase L D.sourceOrbit A
      (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h D A hsect.1 hsect.2 ho hAV
  let e := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hc : Nat.card B.Carrier = 2 ^ (2*n) := by rw [B.card_eq,hfield]
  exact no_hermitian_rank_two_component
    (G := G) (S := D.orbitComponent ⧸ center D.orbitComponent)
    (L := L) (W := D.sourceOrbit) (A := A) (hV ▸ hdata.2.2.1)
    (hV ▸ D.ne_bot) (hV ▸ hdata.2.1)
    (Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent))
    eQ hc π hπ

variable (n : ℕ) [NeZero n]

/-- Residual uniqueness gives ambient odd-normalizer control above field four. -/
theorem sourceOrbit_hermitian_oddNormalizer_le_of_unique
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  exact D.sourceOrbit_hermitian_no_rankTwo_component h hV B eQ hfield A hA ho
    (D.sourceOrbit_hermitian_rankTwo_component_of_unique n h hV d B eQ hfield hn
      A hne hA ho hu hout)

/-- The coordinate version leaves only the original pushing-up configuration. -/
theorem sourceOrbit_hermitian_pushingUp_of_globalR_lt
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
        normalizer (L : Set G) ∧ PushingUpCase L D.sourceOrbit A := by
  obtain ⟨A,hne,hA,ho,ha,hout,hcore,hcases⟩ :=
    D.sourceOrbit_hermitian_refined_oddNormalizer_obstruction n h hmany hV hnon
      d B eQ hfield hn hr
  refine ⟨A,hne,hA,ho,ha,hout,hcore,?_⟩
  exact hcases.resolve_right
    (D.sourceOrbit_hermitian_no_rankTwo_component h.toHypothesis1221 hV B eQ hfield A hA ho)

/-- The literal tensor consumer discharges the entire placed-component alternative. -/
theorem sourceOrbit_hermitian_tensor_pushingUp_of_globalR_lt
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
        normalizer (L : Set G) ∧ PushingUpCase L D.sourceOrbit A := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_pushingUp_of_globalR_lt n h hmany hV hnon
    d B eQ hfield hn hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
