module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianPushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianParabolics

/-!
# Escaping components on the original Hermitian chosen orbit

The inclusion-compatible covering quotient in the original pushing-up pair
transports the chosen orbit component's projective marking to its actual
residual. For n > 1 the contained-Fitting branch is impossible, so the
component selection applies without an extra callback. Every clause of the
original pushing-up configuration is retained, including the chosen module,
its commutator identity, the covering map and its section-centralizer conjugate.

The literal tensor application below reduces r < 4n to these actual escaping
components. Their exclusion, weak closure and the separate field-four endgame
remain with qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith C.2.11--13, C.3.2--4 and C.4.4, pp.148--152,
applied in 4.4.6 and 7.4.1, pp.620,699--700 (refs/quasithin.pdf).
-/

@[expose] public noncomputable section
open scoped Classical IsMulCommutative MatrixGroups Pointwise
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original configuration, with a component selected on the same witnesses. -/
def HermitianPushingUpComponentCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    J ∈ muStar (normalizer (L : Set G)) L
      (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let MH := H ⊓ normalizer (L : Set G)
    let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H MH LH (J.pCoreIn 2) W ∧
    (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
    (LH.subgroupOf MH).Normal ∧
    V = ⁅V,LH⁆ ∧ V ≤ LH ∧
    (∃ e : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
      ∀ i : LH, e (QuotientGroup.mk' (pCore 2 LH) i) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) i)) ∧
    pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
    ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
    generalizedFitting X = pCore 2 X ∧
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
    Nat.card V ≤ Nat.card W ∧
    (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ MH.subgroupOf H ∧
      conjugateSpanBy LH MH ≤ normalizer (K.map H.subtype : Set G) ∧
      ((IsComponent H K ∧ K.Normal ∧ LH.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H (J.pCoreIn 2) MH (K.map H.subtype) ∧
          ChapterC.C27Source.StarModels.Model
            (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))))

variable (D : ChosenModule T L V)

/-- The original covering isomorphism discharges the component-selection premise. -/
theorem sourceOrbit_hermitian_pushingUp_component_case
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    {n : ℕ} (hfield : B.degree = 2*n) (hn : 1 < n)
    {A : Subgroup G} (hc : PushingUpCase L D.sourceOrbit A) :
    HermitianPushingUpComponentCase L D.sourceOrbit A := by
  obtain ⟨J,H,W,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,⟨e,he⟩,
    hcore,hrad,hsyl,hfit,hP,hsize,hVW⟩ := hc
  let := h.quasisimple
  let : IsQuasisimple
      (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ⧸
        pCore 2 ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let es := ((QuotientGroup.congr _ _ e (FixedElementary.map_center e)).trans
    (D.orbitCentralQuotientEquiv h)).trans eQ
  have hcard : Nat.card B.Carrier = 2^(2*n) := by rw [B.card_eq,hfield]
  exact ⟨J,H,W,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,⟨e,he⟩,
    hcore,hrad,hsyl,hfit,hP,hsize,hVW,
    pushingUp_escaping_component hC hstrict hn hcard es⟩

variable (n : ℕ) [NeZero n]

/-- The coordinate reduction selects a component while retaining the original odd actor. -/
theorem sourceOrbit_hermitian_components_of_globalR_lt
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
        normalizer (L : Set G) ∧ HermitianPushingUpComponentCase L D.sourceOrbit A := by
  obtain ⟨A,hne,hA,ho,ha,hout,hcore,hcase⟩ :=
    D.sourceOrbit_hermitian_pushingUp_of_globalR_lt n h hmany hV hnon d B eQ hfield hn hr
  exact ⟨A,hne,hA,ho,ha,hout,hcore,
    D.sourceOrbit_hermitian_pushingUp_component_case h.toHypothesis1221 B eQ hfield hn hcase⟩

/-- The literal tensor marking supplies the component selection without a local callback. -/
theorem sourceOrbit_hermitian_tensor_components_of_globalR_lt
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
        normalizer (L : Set G) ∧ HermitianPushingUpComponentCase L D.sourceOrbit A := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_components_of_globalR_lt n h hmany hV hnon
    d B eQ hfield hn hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
