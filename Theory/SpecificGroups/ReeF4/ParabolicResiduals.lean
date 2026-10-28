module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalIdentification
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.SeedGeneration
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoPowerStability
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableResidual.PrimeTo

/-!
# Generating solvable residuals of the large Ree parabolics

The actual fixed root seeds generate the Ree carrier. Their perfectness,
normality and solvable torus supplements identify them with the embedded
solvable residuals of the full parabolics. Each has nontrivial self-centralizing
two-core and a quasisimple quotient. The Suzuki residual has three-free order;
the linear residual has nonzero triple core commutator. These different
obstructions are retained for applications to the original local family.

All groups are the genuine exceptional fixed-point groups, with parameter
q = 2^(2*m+1), m >= 1. No simplicity premise for the ambient Ree group is
needed. Source: Aschbacher--Smith F.1.12, printed pp.263--264, and the
higher-field argument of 15.1.20(3), printed p.1096 of refs/quasithin.pdf.
The concrete root calculations are proved in the imported model modules.
-/

public section
open Subgroup Theory.GroupTheory
namespace ReeF4.Parabolics
open LargeLocalSeeds
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- The two local factors generate the actual exceptional fixed group. -/
theorem localFactor_sup_eq_top (m : ℕ) :
    localFactor m .suzuki ⊔ localFactor m .linear = ⊤ := by
  rw [←seed_eq_localFactor,←seed_eq_localFactor]
  exact OuterLocal.LargeAutomorphisms.seed_sup_eq_top m

/-- The embedded solvable residual is the actual fixed local factor. -/
theorem parabolic_solvableResidual_map {m : ℕ} (hm : 1 ≤ m) (a : Side) :
    (solvableResidual (parabolic m a)).map (parabolic m a).subtype = localFactor m a := by
  let := OuterLocal.seed_perfect hm a
  let : Group.IsSolvable (fixedTorus m) := by
    rw [←ConverseParabolics.FullLeviRepresentation.torusHom_range]
    exact Group.isSolvable_of_surjective
      (ConverseParabolics.FullLeviRepresentation.torusHom m).rangeRestrict_surjective
  rw [parabolic_eq_seed_sup_fixedTorus]
  rw [map_solvableResidual_sup_eq_of_perfect_normalized]
  · exact seed_eq_localFactor m a
  · exact ((show fixedTorus m ≤ borel m from comap_mono le_sup_right).trans
      (borel_le_parabolic m a)).trans
      (parabolic_le_seed_normalizer_of_splitTorus m a (splitTorus_le_seed_normalizer m a))

/-- Each local residual has characteristic two. -/
theorem localFactor_generalizedFitting {m : ℕ} (hm : 1 ≤ m) (a : Side) :
    generalizedFitting (localFactor m a) = pCore 2 (localFactor m a) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (localFactorStandardSeedEquiv m a)).mpr
  cases a with
  | suzuki => exact suzuki_core_centralizer_le hm _
  | linear => exact linearCore_centralizer_le hm _

/-- Both residuals have nontrivial two-core. -/
theorem localFactor_core_ne_bot {m : ℕ} (hm : 1 ≤ m) (a : Side) :
    pCore 2 (localFactor m a) ≠ ⊥ := by
  intro hb
  let e := localFactorStandardSeedEquiv m a
  have he : pCore 2 (standardSeed (canonicalLocalBlockInput m) a) = ⊥ := by
    rw [←pCore_map_iso 2 e,hb,Subgroup.map_bot]
  cases a with
  | suzuki => exact suzuki_core_ne_bot hm _ he
  | linear => exact linearCore_ne_bot hm _ he

/-- Both literal two-core quotients are quasisimple. -/
theorem localFactor_quotient_quasisimple {m : ℕ} (hm : 1 ≤ m) (a : Side) :
    IsQuasisimple (localFactor m a ⧸ pCore 2 (localFactor m a)) := by
  let := OuterLocal.localFactor_perfect hm a
  let : IsSimpleGroup (localFactor m a ⧸ pCore 2 (localFactor m a)) := by
    cases a with
    | suzuki =>
      let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
      exact (suzukiLocalQuotientEquiv m).isSimpleGroup
    | linear =>
      let := linearQuotient_simple m hm
      exact (linearLocalQuotientEquiv m).isSimpleGroup
  have hz : center (localFactor m a ⧸ pCore 2 (localFactor m a)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center (localFactor m a ⧸ pCore 2 (localFactor m a))) inferInstance with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- The linear residual has nonzero triple core commutator. -/
theorem linearLocalFactor_core_triple {m : ℕ} (hm : 1 ≤ m) :
    ⁅⁅pCore 2 (localFactor m .linear), (⊤ : Subgroup (localFactor m .linear))⁆,
      pCore 2 (localFactor m .linear)⁆ ≠ ⊥ := by
  intro hh
  let e := localFactorStandardSeedEquiv m .linear
  have he := congrArg (Subgroup.map e.toMonoidHom) hh
  rw [map_commutator,map_commutator,pCore_map_iso,←MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr e.surjective,Subgroup.map_bot] at he
  exact linearCore_iterated_commutator_ne_bot hm _ he

/-- The Suzuki residual has no element of order three. -/
theorem suzukiLocalFactor_three_free {m : ℕ} (hm : 1 ≤ m) :
    ¬ 3 ∣ Nat.card (localFactor m .suzuki) := by
  intro hd
  apply ConverseParabolics.suzuki_parabolic_three_free hm
  have hc := card_dvd_of_le (localFactor_le_parabolic m .suzuki)
  rw [←parabolic_eq_rootParabolic] at hc
  exact hd.trans hc

/-- Full parabolics are proper in the large Ree group. -/
theorem parabolic_ne_top {m : ℕ} (hm : 1 ≤ m) (a : Side) :
    parabolic m a ≠ ⊤ := by
  rw [←parabolic_eq_rootParabolic]
  exact (octagonGeometry m hm).parabolic_ne_top a

end ReeF4.Parabolics
