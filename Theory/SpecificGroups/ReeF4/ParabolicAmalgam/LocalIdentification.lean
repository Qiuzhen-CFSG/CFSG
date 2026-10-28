module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore

/-!
# Intrinsic local quotients of the concrete Ree parabolics

The source factors are the embedded O^{2′} of the full parabolics. Root
geometry identifies these with the fixed seeds. The matrix-preserving seed
comparison therefore carries each proved radical kernel to the corresponding
source factor, where it is exactly O₂. The resulting quotient equivalences
retain the concrete projection formulas on representatives. Root-coordinate
counts give orders q^10 and q^11 for these intrinsic cores.

At m = 0 the binary projections have targets Sz(2), the actual order-twenty
Suzuki matrix group, and PSL₂(2). The ambient carrier is the full ²F₄(2),
not its Tits derived subgroup. No Ree simplicity or projection premise is
left in these results. Relative core normality is inside the local factor.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263/PDF p.274 of
`refs/quasithin.pdf`; the binary convention is explained on pp.263–264.
The source amalgam consumer is `GreenBook/LieModels/ReeFour.lean`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics
open Subgroup LargeLocalSeeds BenderSuzuki.MatrixGroups

/-- The root radical is the intrinsic core in the source local factor. -/
theorem localRadical_eq_pCore (m : ℕ) (s : Side) :
    localRadical m s = pCore 2 (localFactor m s) := by
  unfold localRadical
  rw [← seed_eq_localFactor]
  change radicalInSeed m s = pCore 2 (seed m s)
  cases m with
  | zero => exact Binary.radicalInSeed_eq_pCore s
  | succ m =>
    rw [← seedRadical_map_seedEquiv]
    have h : seedRadical (canonicalLocalBlockInput (m + 1)) s =
        pCore 2 (standardSeed (canonicalLocalBlockInput (m + 1)) s) := by
      cases s with
      | suzuki => exact suzuki_seedRadical_eq_pCore (by omega) _
      | linear => exact seedRadical_linear_eq_twoCore (by omega) _
    rw [h, pCore_map_iso]

/-- Equality with the root seed, preserving its ambient group elements. -/
def localFactorSeedEquiv (m : ℕ) (s : Side) : localFactor m s ≃* seed m s :=
  MulEquiv.subgroupCongr (seed_eq_localFactor m s).symm

/-- Comparison with the fixed matrix seed used by the projection calculations. -/
def localFactorStandardSeedEquiv (m : ℕ) (s : Side) :
    localFactor m s ≃* standardSeed (canonicalLocalBlockInput m) s :=
  (localFactorSeedEquiv m s).trans (seedEquiv m s).symm

/-- The Suzuki quotient of the actual source factor, including Sz(2). -/
def suzukiLocalQuotientEquiv (m : ℕ) :
    (localFactor m .suzuki ⧸ pCore 2 (localFactor m .suzuki)) ≃* SuzukiMatrixGroup m := by
  cases m with
  | zero =>
    exact (QuotientGroup.congr _ _ (localFactorSeedEquiv 0 .suzuki)
      (pCore_map_iso 2 _)).trans Binary.suzukiCoreQuotientEquiv
  | succ m =>
    exact (QuotientGroup.congr _ _ (localFactorStandardSeedEquiv (m + 1) .suzuki)
      (pCore_map_iso 2 _)).trans (suzuki_coreQuotientEquiv (by omega) _)

/-- The linear quotient over the exact field of order 2^(2*m+1). -/
def linearLocalQuotientEquiv (m : ℕ) :
    (localFactor m .linear ⧸ pCore 2 (localFactor m .linear)) ≃* LinearQuotient m := by
  cases m with
  | zero =>
    exact (QuotientGroup.congr _ _ (localFactorSeedEquiv 0 .linear)
      (pCore_map_iso 2 _)).trans Binary.linearCoreQuotientEquiv
  | succ m =>
    exact (QuotientGroup.congr _ _ (localFactorStandardSeedEquiv (m + 1) .linear)
      (pCore_map_iso 2 _)).trans (linearCoreQuotientEquiv (by omega) _)

@[simp] theorem suzukiLocalQuotientEquiv_zero_mk (x : localFactor 0 .suzuki) :
    suzukiLocalQuotientEquiv 0 (QuotientGroup.mk' (pCore 2 (localFactor 0 .suzuki)) x) =
      BinarySuzuki.projection (localFactorSeedEquiv 0 .suzuki x) := rfl

@[simp] theorem linearLocalQuotientEquiv_zero_mk (x : localFactor 0 .linear) :
    linearLocalQuotientEquiv 0 (QuotientGroup.mk' (pCore 2 (localFactor 0 .linear)) x) =
      BinaryLinear.projection (localFactorSeedEquiv 0 .linear x) := rfl

@[simp] theorem suzukiLocalQuotientEquiv_succ_mk (m : ℕ) (x : localFactor (m + 1) .suzuki) :
    suzukiLocalQuotientEquiv (m + 1)
      (QuotientGroup.mk' (pCore 2 (localFactor (m + 1) .suzuki)) x) =
      SuzukiLeviProjection.projection (canonicalLocalBlockInput (m + 1))
        (localFactorStandardSeedEquiv (m + 1) .suzuki x) := rfl

@[simp] theorem linearLocalQuotientEquiv_succ_mk (m : ℕ) (x : localFactor (m + 1) .linear) :
    linearLocalQuotientEquiv (m + 1)
      (QuotientGroup.mk' (pCore 2 (localFactor (m + 1) .linear)) x) =
      LinearProjection.projection (by omega) (canonicalLocalBlockInput (m + 1))
        (localFactorStandardSeedEquiv (m + 1) .linear x) := by
  change linearCoreQuotientEquiv _ _ (QuotientGroup.mk' _ _) = _
  exact linearCoreQuotientEquiv_mk _ _ _

/-- Embedding the local two-core recovers the specified ambient root radical. -/
theorem local_pCore_map (m : ℕ) (s : Side) :
    (pCore 2 (localFactor m s)).map (localFactor m s).subtype = radical m s := by
  rw [← localRadical_eq_pCore]
  exact localRadical_map m s

theorem card_local_pCore_suzuki (m : ℕ) :
    Nat.card (pCore 2 (localFactor m .suzuki)) = (2 ^ (2 * m + 1)) ^ 10 := by
  rw [← localRadical_eq_pCore]
  exact card_localRadical_suzuki m

theorem card_local_pCore_linear (m : ℕ) :
    Nat.card (pCore 2 (localFactor m .linear)) = (2 ^ (2 * m + 1)) ^ 11 := by
  rw [← localRadical_eq_pCore]
  exact card_localRadical_linear m

end ReeF4.Parabolics
