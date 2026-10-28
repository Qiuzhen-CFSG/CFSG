module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictCrossingKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictRank

/-!
# Crossing quotient ranks on the whole reduced layer

The original source hypotheses construct the moving residual cubic and both
elementary quotient structures. The center-image order, exact rank identity
and G.10.2 inequalities concern the original U/Z(U) and X-dot/Z(U)^d-dot.
Thus G.10.1(2b)'s numerical premise is discharged on the actual Chapter12 layer.

Source: Aschbacher--Smith, 6.2.17(10), 6.2.18 and 12.2.2(3d).
The remaining fixed-vector and classification argument is owned by
qt-d-1222-recognition-strict-elimination. LocalAnalysis is supplied by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The actual quotient-rank condition and its consequences for the whole
reduced layer, without an additional dimension or action-kernel input. -/
theorem strict_reduced_crossing_quotient_rank
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
      Nat.card (strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d) * 2 =
        Nat.card (center (sourceClosure (T : Subgroup G) L (wholeReduced T L) z)) ∧
      ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
        letI := he
        ∃ hX : IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d),
          letI := hX
          let X := strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d
          let X₀ := (strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d).subgroupOf X
          let r := Group.rank (X ⧸ X₀)
          let m := Module.finrank (ZMod 2)
            (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z))
          Module.finrank (ZMod 2) (strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
            (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d)) + r + 1 = m ∧
          0 < r ∧ 4 ≤ m ∧ m ≤ 2 * (r + 1) ∧
            2 * (r + 1) ≤ 2 * (primeRank 2 (StrictActor (T : Subgroup G) L (wholeReduced T L) z) + 1) := by
  obtain ⟨d, hdres, hdL, _, hdZ, hd3, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he, _⟩ := A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  let hX := A.strict_crossingImage_elementary h611 hnatural hz horder hstrict hdZ
  let := hX
  exact ⟨d, hdres, hdL, hd3, hdH,
    A.strict_crossing_center_image_card h611 hnatural hz horder hTH hstrict hdres hdH,
    he, hX,
    A.strict_crossing_quotient_rank h611 hnatural hz horder hTH hstrict hdres hdH,
    A.strict_crossing_rank_bounds h611 hnatural hz horder hTH hstrict hdres hdH⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
