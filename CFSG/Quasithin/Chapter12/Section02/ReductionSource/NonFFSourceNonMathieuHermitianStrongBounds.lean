module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianOrdinary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianOrdinary


/-!
# The strong Hermitian r-bound on the original chosen orbit

For n > 1 the ordinary component in the literal pushing-up configuration is
impossible: its actual central quotient has no compatible local PSL₃(2^(2n))
section. Together with the previously checked constrained and placed-component
exclusions this proves r >= 4n, without an odd-normalizer callback. Descent of
the original half-field tensor supplies the coordinates for the final consumer.

The weak-closure and torus arguments and the separate field-four endgame remain
open. No statement here excludes half-degree one.
Source: Aschbacher--Smith C.3.1, 4.4.3 and 7.4.1, printed pp.149--151,
619--623 and 699--700 (refs/quasithin.pdf).
-/

public noncomputable section
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
variable (D : ChosenModule T L V)

/-- The ordinary component is excluded on the original residual and module witnesses. -/
theorem sourceOrbit_no_hermitian_ordinary_case
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    {n : ℕ} (hfield : B.degree = 2*n) (hn : 1 < n) (A : Subgroup G) :
    ¬ HermitianPushingUpOrdinaryCase L D.sourceOrbit A := by
  rintro ⟨J,H,W,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,⟨e,he⟩,
    hcore,hrad,hsyl,hfit,hP,hsize,hVW,K,hK,_⟩
  let := h.quasisimple
  let : IsQuasisimple
      (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ⧸
        pCore 2 ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let es := ((QuotientGroup.congr _ _ e (FixedElementary.map_center e)).trans
    (D.orbitCentralQuotientEquiv h)).trans eQ
  have hcard : Nat.card B.Carrier = 2^(2*n) := by rw [B.card_eq,hfield]
  exact no_ordinary_hermitian_component hC hn hcard es K hK

variable (n : ℕ) [NeZero n]

/-- The stronger 7.4.1 bound with no remaining local configuration premise. -/
theorem sourceOrbit_hermitian_globalR_ge_four_mul
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) :
    ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  by_contra! hr
  obtain ⟨A,_,_,_,_,_,_,hc⟩ :=
    D.sourceOrbit_hermitian_ordinary_of_globalR_lt n h hmany hV hnon d B eQ hfield hn hr
  exact D.sourceOrbit_no_hermitian_ordinary_case h.toHypothesis1221 B eQ hfield hn A hc

/-- The literal tensor marking proves the strong r-bound on the original action and T. -/
theorem sourceOrbit_hermitian_tensor_globalR_ge_four_mul
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
    (hn : 1 < n) : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
