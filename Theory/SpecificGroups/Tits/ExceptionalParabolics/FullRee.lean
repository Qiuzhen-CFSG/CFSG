module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The marked parabolics in the full binary Ree matrix group

The numerator groups are the actual fixed root seeds in `ReeF4.Model 0`.
At the binary endpoint these seeds equal both the full parabolics and their
prime-to-two residuals. The Borel is the positive Sylow two-subgroup and is
exactly their intersection. The two root projections identify the intrinsic
cores and their actual matrix quotients, with their formulas retained.

This constructs the full Ree local model in F.1.12(I)(5) at q = 2. It does
not identify its carrier with all automorphisms of the Atlas Tits group:
that requires the independent derived-action coverage and marked comparison.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, and 14.2.21,
printed pp.988--989; GLS3, §§2.3--2.4. The root-coordinate calculations and
projections are proved in the imported Ree modules.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee

open Theory.GroupTheory ReeF4 ReeF4.Parabolics

abbrev S : Subgroup (Model 0) := unipotent 0
abbrev B : Subgroup (Model 0) := borel 0
abbrev first : Subgroup (Model 0) := seed 0 .suzuki
abbrev second : Subgroup (Model 0) := seed 0 .linear

/-- Each specified local group is its full binary parabolic. -/
theorem first_eq_parabolic : first = parabolic 0 .suzuki := (parabolic_zero _).symm

theorem second_eq_parabolic : second = parabolic 0 .linear := (parabolic_zero _).symm

/-- These local groups are also the source prime-to-two residuals. -/
theorem first_eq_localFactor : first = localFactor 0 .suzuki := seed_eq_localFactor _ _

theorem second_eq_localFactor : second = localFactor 0 .linear := seed_eq_localFactor _ _

theorem borel_eq_sylow : B = S := borel_zero

theorem sylow_le_first : S ≤ first := unipotent_le_seed _ _
theorem sylow_le_second : S ≤ second := unipotent_le_seed _ _

theorem borel_le_first : B ≤ first := by rw [borel_eq_sylow]; exact sylow_le_first

theorem borel_le_second : B ≤ second := by rw [borel_eq_sylow]; exact sylow_le_second

/-- The marked Borel is the whole common overlap. -/
theorem overlap_eq_borel : first ⊓ second = B := by
  simpa only [parabolic_zero] using parabolic_inf_eq_borel 0

def sylow : Sylow 2 (Model 0) := Binary.sylow

theorem sylow_coe : (sylow : Subgroup (Model 0)) = S := Binary.sylow_coe

theorem sylow_card : Nat.card S = 4096 := by
  simpa using card_unipotent 0

theorem borel_card : Nat.card B = 4096 := by rw [borel_eq_sylow, sylow_card]

theorem generate : first ⊔ second = ⊤ := Binary.seed_sup_eq_top

/-- The full binary Ree amalgam uses its actual Borel and both inclusions. -/
def amalgam : RankTwoAmalgam first B second :=
  RankTwoAmalgam.ofSubgroups first B second borel_le_first borel_le_second

theorem amalgam_left_injective : Function.Injective amalgam.left :=
  Subgroup.inclusion_injective borel_le_first

theorem amalgam_right_injective : Function.Injective amalgam.right :=
  Subgroup.inclusion_injective borel_le_second

/-- The concrete Suzuki projection, with no abstract replacement of its target. -/
abbrev firstProjection : first →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  BinarySuzuki.projection

abbrev secondProjection : second →* LargeLocalSeeds.LinearQuotient 0 :=
  BinaryLinear.projection

theorem firstProjection_surjective : Function.Surjective firstProjection :=
  BinarySuzuki.projection_surjective

theorem secondProjection_surjective : Function.Surjective secondProjection :=
  BinaryLinear.projection_surjective

theorem firstProjection_ker : firstProjection.ker = pCore 2 first :=
  Binary.suzuki_projection_ker_pCore

theorem secondProjection_ker : secondProjection.ker = pCore 2 second :=
  Binary.linear_projection_ker_pCore

/-- The first quotient is the actual Sz(2) matrix group. -/
def firstCoreQuotientEquiv :
    (first ⧸ pCore 2 first) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  Binary.suzukiCoreQuotientEquiv

/-- The second quotient is PSL₂ over the specified field with two elements. -/
def secondCoreQuotientEquiv :
    (second ⧸ pCore 2 second) ≃* LargeLocalSeeds.LinearQuotient 0 :=
  Binary.linearCoreQuotientEquiv

@[simp] theorem firstCoreQuotientEquiv_mk (x : first) :
    firstCoreQuotientEquiv (QuotientGroup.mk' (pCore 2 first) x) = firstProjection x := rfl

@[simp] theorem secondCoreQuotientEquiv_mk (x : second) :
    secondCoreQuotientEquiv (QuotientGroup.mk' (pCore 2 second) x) = secondProjection x := rfl

private theorem core_card (s : LargeLocalSeeds.Side) :
    Nat.card (pCore 2 (seed 0 s)) = Nat.card (radical 0 s) := by
  rw [← Binary.radicalInSeed_eq_pCore]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    ((radical_le_unipotent 0 s).trans (unipotent_le_seed 0 s))).toEquiv

/-- Core orders are intrinsic to the two full parabolics. -/
theorem first_core_card : Nat.card (pCore 2 first) = 1024 := by
  rw [core_card, card_radical_suzuki]
  norm_num

theorem second_core_card : Nat.card (pCore 2 second) = 2048 := by
  rw [core_card, card_radical_linear]
  norm_num

end Tits.ExceptionalParabolics.FullRee
