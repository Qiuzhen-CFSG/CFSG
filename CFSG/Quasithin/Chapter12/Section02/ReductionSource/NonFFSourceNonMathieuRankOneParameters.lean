module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneHeldBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneComplete
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure

/-!
# Suzuki higher Thompson control and the lower weak-closure bound

The full automizer's natural fixed-codimension and rank bounds exclude
near offenders, hence J_1(X) centralizes the orbit whenever X contains and
normalizes it. Applied to the literal local centralizers, this discharges
the Thompson premise of E.6.27. Completed odd-local control and the initial
E.6.3 bound leave only the intrinsic odd Cartan bound in that application.
The same initial estimate and a <= n prove the source lower bound w >= n.
The upper w bound, odd-element estimate, stronger r bound and final two
exclusions remain with qt-d-1222-nonmathieu-unitary-suzuki-exclusion.
Source: Aschbacher--Smith 7.2.1, 7.3.2--3, 7.4.1 and E.6.27,
printed pp.698--700,257.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_suzuki_no_near_offender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim (automizerRepresentation D.sourceOrbit) A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hr := (offender_rank_le_primeRank A).trans (D.sourceOrbit_suzuki_automizer_rank h hs hm e)
  rw [D.sourceOrbit_suzuki_automizer_fixedCodim h hs hm e A hA]
  omega

theorem sourceOrbit_suzuki_thompson_one_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (X : Subgroup G) (hWX : D.sourceOrbit ≤ X)
    (hXN : X ≤ normalizer (D.sourceOrbit : Set G)) :
    thompsonJ X 1 ≤ centralizer (D.sourceOrbit : Set G) :=
  thompson_centralizes_of_fixedCodim_gap D.sourceOrbit X hWX hXN
    (D.sourceOrbit_suzuki_no_near_offender h hs hm e)

theorem sourceOrbit_suzuki_localCentralizer_thompson_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) :
    thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  exact le_inf ((thompsonJ_le _ _).trans inf_le_left)
    (D.sourceOrbit_suzuki_thompson_one_centralizes h hs hm e _
      (h61.normal_in_localCentralizer hU hUW).1 (h61.localCentralizer_le_normalizer hU hUW))

/-- E.6.27 with its ambient and higher-Thompson inputs discharged. -/
theorem sourceOrbit_suzuki_centralizer_le_of_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hn : nPrime (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hr := (D.sourceOrbit_suzuki_initial_parameters h hmany hV hs hnon hm e).1
  apply D.sourceOrbit_suzuki_centralizer_le h hmany hV hs hnm hnon hm e hU hUW (by decide) ?_ hn
    (D.sourceOrbit_suzuki_localCentralizer_thompson_one h hmany hV hs hnon hm e hU hUW)
  exact lt_of_lt_of_le (by exact_mod_cast (show 1 < 2 * (2 * m + 1) by omega)) hr

theorem sourceOrbit_suzuki_localA
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    localA D.sourceOrbit ≤ (2 * m + 1 : ℕ) :=
  (localA_le_automizer_rank D.sourceOrbit).trans
    (ENat.natCast_le_natCast.mpr (D.sourceOrbit_suzuki_automizer_rank h hs hm e))

/-- The actual lower w-column of Table 7.2.1, on the original Sylow. -/
theorem sourceOrbit_suzuki_globalW_lower
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    (2 * m + 1 : ℕ) ≤ globalW D.sourceOrbit T := by
  have hi := D.sourceOrbit_suzuki_initial_parameters h hmany hV hs hnon hm e
  have hS : ((2 * (2 * m + 1) : ℕ) : ℕ∞) ≤ globalS D.sourceOrbit := by
    rw [hi.2.1]
    exact ENat.natCast_le_natCast.mpr (D.sourceOrbit_suzuki_localM h hs hm e)
  have hb := hS.trans (Chapter7.globalS_le_globalW_add_localA D.sourceOrbit_weakClosure_setup)
  have hb' := hb.trans (add_le_add le_rfl (D.sourceOrbit_suzuki_localA h hs hm e))
  by_contra hn
  have hw : globalW D.sourceOrbit T < (2 * m + 1 : ℕ) := lt_of_not_ge hn
  have hc : globalW D.sourceOrbit T + (2 * m + 1 : ℕ) <
      ((2 * (2 * m + 1) : ℕ) : ℕ∞) := by
    calc
      _ < ((2 * m + 1 : ℕ) : ℕ∞) + ((2 * m + 1 : ℕ) : ℕ∞) :=
        (ENat.add_lt_add_iff_right (ENat.natCast_ne_top (2 * m + 1))).mpr hw
      _ = _ := by rw [← Nat.cast_add, ← two_mul]
  exact (not_lt_of_ge hb') hc
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
