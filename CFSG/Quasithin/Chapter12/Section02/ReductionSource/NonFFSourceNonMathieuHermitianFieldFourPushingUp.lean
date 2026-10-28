module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianOrdinary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourExtraPlacement

/-!
# Field-four pushing-up at the actual Hermitian extraspecial centers

The inclusion-compatible covering quotient identifies the original pushing-up
residual's central quotient with PSL₃(4). Its contained-Fitting and constrained
branches are excluded on those same witnesses, so failure of uniqueness gives
an ordinary component containing both that residual and the moved module.

The tensor application retains the same four-space, residual, containing
C-component, extraspecial Sylow supplements and their embedded centers on both
weak-closure branches. Every actual center is now in the residual-uniqueness
branch or the ordinary pushing-up branch. Whole odd-normalizer control still
requires exclusion of these remaining configurations.

Source: Aschbacher--Smith 4.4.3, Remark 4.4.2 and 8.2.7, printed
pp.619,717--718; the pushing-up selection uses C.2.8--13 and C.4.4,
printed pp.147--152, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original covering isomorphism excludes all constrained component alternatives. -/
theorem sourceOrbit_hermitian_field_four_pushingUp_ordinary_case
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
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
  have hcard : Nat.card B.Carrier = 4 := by rw [B.card_eq,hfield]; decide
  exact ⟨J,H,W,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,⟨e,he⟩,
    hcore,hrad,hsyl,hfit,hP,hsize,hVW,
    field_four_pushingUp_ordinary hC hstrict hN hcard es⟩

/-- Failure of uniqueness selects an ordinary component on the original witnesses. -/
theorem sourceOrbit_hermitian_field_four_oddActor_alternatives
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∨
      HermitianPushingUpOrdinaryCase L D.sourceOrbit A := by
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · exact Or.inl hu
  · exact Or.inr (D.sourceOrbit_hermitian_field_four_pushingUp_ordinary_case h B eQ hfield
      (D.sourceOrbit_pushingUp_case_of_not_unique h hV A hA ho hu))

/-- The literal tensor selects the remaining configurations for every actual center. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_center_alternatives
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
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K) ∧
          (Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
            ∀ (p : ℕ) (_ : Fact p.Prime),
              p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
              Chapter1.Section02.LocalModels.OddExtraspecialThree p
                (pCore p (Chapter1.XiQuotient K)) ∧
              IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)) ∧
              Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p ∧
              (Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
                Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
                (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) =
                  (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (L : Set G) ∧
                ∀ P : Sylow p (Chapter1.XiP p K),
                  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
                  let Z := (center Y).map Y.subtype
                  Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                    Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
                    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
                    (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
                      normalizer (L : Set G) ∧
                    (UniqueMaximalOvergroup (oddActorResidual L Z) (normalizer (L : Set G)) ∨
                      HermitianPushingUpOrdinaryCase L D.sourceOrbit Z))) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_centers
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  let := hU
  refine ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp,hH,heq,hcenters⟩ := hcores hnil p hp hd
  have hgt := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  refine ⟨hfull,hx,hcard,hexp,hH,heq,?_⟩
  intro P
  obtain ⟨hc,hcyc,hne,hplaced,hout,hcore⟩ := hcenters P
  exact ⟨hc,hcyc,hne,hplaced,hout,hcore,
    D.sourceOrbit_hermitian_field_four_oddActor_alternatives
      h.toHypothesis1221 hV B eQ hB _ hplaced (by rwa [hc])⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
