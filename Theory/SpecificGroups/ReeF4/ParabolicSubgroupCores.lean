module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.Suzuki.NormalSubgroups
public import Theory.SpecificGroups.ReeF4.ParabolicSubgroupCores.Linear
public import Theory.SpecificGroups.ReeF4.ParabolicSubgroupCores.Transfer

/-!
# Two-cores of nonsolvable subgroups of full Ree parabolics

For positive Ree parameter, the intrinsic two-core of a nonsolvable subgroup
of either full parabolic lies in its root-defined radical. The full Levi
projections have targets SL₂(q) × Fqˣ and Sz(q) × Fqˣ and exactly those
radicals as their two-group kernels. Nonsolvability therefore survives in
the rank-one projection. The SL₂ fixed-line argument and the Suzuki
normal-subgroup theorem kill the core's rank-one image; the complementary
field torus has no nonidentity elements of two-power order.

The parabolic and radical comparisons identify the actual matrix subgroups
with the root conventions used by the consumer. This discharges the
subgroup-core premise in the Ree E2 confinement argument; long-root
intersection saturation is a separate geometric statement.

Sources: Aschbacher--Smith F.1.12(I)(5), printed pp.263--264 / PDF pp.274--275,
and E.1.14(1), printed p.214, citing Aschbacher (1982), Lemma 4.7
(`refs/quasithin.pdf`); GLS3 §§2.3--2.6, especially Theorem 2.6.5
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

namespace ReeF4.ParabolicSubgroupCores
open Subgroup
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open BenderSuzuki.MatrixGroups

private theorem units_pow_two_eq_one {F : Type*} [Field F] [CharP F 2]
    (t : Fˣ) (k : ℕ) (h : t ^ (2 ^ k) = 1) : t = 1 := by
  apply Units.ext
  exact (iterateFrobenius_inj F 2 k) (by
    simpa [iterateFrobenius_def] using congrArg Units.val h)

private theorem suzuki_twoCore_eq_bot {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hH : ¬ Group.IsSolvable H) :
    pCore 2 H = ⊥ := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  exact suzukiSubgroup_solvable_normal_eq_bot hm H hH (pCore 2 H)

/-- The two-core of a nonsolvable subgroup of either full Ree parabolic
lies in the specified root radical. Normality is only inside the subgroup. -/
theorem pCoreIn_le_radical {m : ℕ} (hm : 0 < m) (s : LargeLocalSeeds.Side)
    (J : Subgroup (Model m)) (hJ : J ≤ Parabolics.parabolic m s)
    (hns : ¬ Group.IsSolvable J) : J.pCoreIn 2 ≤ Parabolics.radical m s := by
  rw [← parabolic_eq_rootParabolic] at hJ
  rw [← ConverseParabolics.radical_eq_rootRadical]
  cases s with
  | linear =>
    exact pCoreIn_le_of_rankOne_product _ _ J hJ
      (ConverseParabolics.linearProjection hm)
      (ConverseParabolics.linearProjection_ker hm)
      (ConverseParabolics.linearProjection_ker_isPGroup hm)
      units_pow_two_eq_one
      Matrix.SpecialLinearGroup.twoCore_eq_bot_of_not_isSolvable hns
  | suzuki =>
    exact pCoreIn_le_of_rankOne_product _ _ J hJ
      (ConverseParabolics.suzukiProjection hm)
      (ConverseParabolics.suzukiProjection_ker hm)
      (ConverseParabolics.suzukiProjection_ker_isPGroup hm)
      units_pow_two_eq_one (suzuki_twoCore_eq_bot hm) hns
end ReeF4.ParabolicSubgroupCores
