module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianConstrained
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianParabolics

/-!
# Ordinary components on the original Hermitian chosen orbit

For n > 1 the actual constrained star models are all excluded. The original
pushing-up residual therefore lies in an ordinary component of the same H.
Every covering, module and radical witness of the original configuration is
retained. The literal half-field tensor input supplies this conclusion when
r < 4n, with no additional action or normality premise.

The ordinary-component exclusion, weak closure and field-four endgame remain
with qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith C.2.11--13, C.3.2--4 and C.4.5--8, pp.148--154,
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

/-- The original configuration, with an ordinary component on the same witnesses. -/
def HermitianPushingUpOrdinaryCase (L V A : Subgroup G) : Prop :=
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
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ ¬ K ≤ MH.subgroupOf H ∧
      LH.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K

variable (D : ChosenModule T L V)

/-- The original covering isomorphism excludes all constrained component alternatives. -/
theorem sourceOrbit_hermitian_pushingUp_ordinary_case
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    {n : ℕ} (hfield : B.degree = 2*n) (hn : 1 < n)
    {A : Subgroup G} (hc : PushingUpCase L D.sourceOrbit A) :
    HermitianPushingUpOrdinaryCase L D.sourceOrbit A := by
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
    pushingUp_ordinary_component hC hstrict hN hn hcard es⟩

variable (n : ℕ) [NeZero n]

/-- The coordinate reduction selects an ordinary component with the original odd actor. -/
theorem sourceOrbit_hermitian_ordinary_of_globalR_lt
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
        normalizer (L : Set G) ∧ HermitianPushingUpOrdinaryCase L D.sourceOrbit A := by
  obtain ⟨A,hne,hA,ho,ha,hout,hcore,hcase⟩ :=
    D.sourceOrbit_hermitian_pushingUp_of_globalR_lt n h hmany hV hnon d B eQ hfield hn hr
  exact ⟨A,hne,hA,ho,ha,hout,hcore,
    D.sourceOrbit_hermitian_pushingUp_ordinary_case h.toHypothesis1221 B eQ hfield hn hcase⟩

/-- The literal tensor marking supplies the ordinary component without a local callback. -/
theorem sourceOrbit_hermitian_tensor_ordinary_of_globalR_lt
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
        normalizer (L : Set G) ∧ HermitianPushingUpOrdinaryCase L D.sourceOrbit A := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_ordinary_of_globalR_lt n h hmany hV hnon
    d B eQ hfield hn hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
