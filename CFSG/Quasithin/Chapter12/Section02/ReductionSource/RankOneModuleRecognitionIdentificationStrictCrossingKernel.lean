module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictBinaryModule
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingKernel

/-!
# The original crossing-action kernel on the whole reduced layer

The source Frattini argument and the natural opposite-factor module identify
the kernel on X with E. Thus the literal map to H/C_H(U/Z(U)) induces the
marked isomorphism X/E ≃ X-dot. The original X lies in the original Sylow
subgroup, and its intersection with O₂(H) is the same E.

Source: Aschbacher--Smith, 6.2.17(6), printed pp.689--690, and 12.2.2(3d).
The fixed bound on U/Z(U), quotient-rank identity and classification
elimination remain with qt-d-1222-recognition-strict-elimination.
LocalAnalysis is supplied by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The exact original crossing kernel and its quotient map, with no
additional local-action premise. -/
theorem strict_reduced_crossing_action_kernel
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L),
      d ∈ L ∧ orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) ∧
      strictCrossingGroup (T : Subgroup G) L (wholeReduced T L) z d ≤ (T : Subgroup G) ∧
      strictCrossingGroup (T : Subgroup G) L (wholeReduced T L) z d ⊓
        (centralizer ({z} : Set G)).pCoreIn 2 =
        strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d ∧
      strictCrossingGroup (T : Subgroup G) L (wholeReduced T L) z d ⊓
        (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker.map
          (centralizer ({z} : Set G)).subtype =
        strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d ∧
    let X := strictCrossingGroup (T : Subgroup G) L (wholeReduced T L) z d
    let E := strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d
    ∃ hN : (E.subgroupOf X).Normal,
      letI := hN
      ∃ e : (X ⧸ E.subgroupOf X) ≃* strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d,
        ∀ x : X, (e (QuotientGroup.mk' (E.subgroupOf X) x) : StrictActor (T : Subgroup G) L (wholeReduced T L) z) =
          QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker
            ⟨x, strictCrossingGroup_le_centralizer _ _ _ _ _ hz x.property⟩ := by
  obtain ⟨d, hdres, hdL, _, _, hd3, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  exact ⟨d, hdres, hdL, hd3, hdH,
    A.strict_crossing_le_sylow h611 hnatural hz horder hTH hstrict hdres hdH,
    A.strict_crossing_core_intersection h611 hnatural hz horder hTH hstrict hdres hdH,
    A.strict_crossing_action_kernel h611 hnatural hz horder hTH hstrict hdres hdH,
    A.strict_crossing_quotient_equiv h611 hnatural hz horder hTH hstrict hdres hdH⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
