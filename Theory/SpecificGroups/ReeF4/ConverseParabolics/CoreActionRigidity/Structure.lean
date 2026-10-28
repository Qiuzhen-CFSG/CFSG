module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Core
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Intrinsic cores and seed comparisons for the full Ree parabolics

Both full parabolics have self-centralizing two-core. Relative normality and
self-centralization of their root radicals imply this without ambient simplicity.
The Suzuki-side projection has a two-group kernel and target Suzuki matrices
times the field units. Both target factors have three-free order, so the full
parabolic does too; no Ree order formula is used.

The actual matrix-preserving seed inclusion carries the linear seed two-core
onto the entire full-parabolic root radical. It carries the perfect seed and
its nonzero iterated radical commutator into the same parabolic. These maps
retain the complementary torus and do not identify the seed with the full group.

Sources: Aschbacher–Smith F.1.12(I)(5) and (II), printed pp.263–264, and the
Ree exclusion in 2.3.9(7), printed p.526. These intrinsic calculations support
the invariant-parabolic argument in E.6.8, printed pp.247–248, of
`refs/quasithin.pdf` (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup
namespace ReeF4.ConverseParabolics

/-- Characteristic two for both full parabolics, including their complementary tori. -/
theorem parabolic_centralizer_pCore_le {m : ℕ} (hm : 1 ≤ m)
    (s : LargeLocalSeeds.Side) :
    centralizer (pCore 2 (parabolic m s) : Set (parabolic m s)) ≤
      pCore 2 (parabolic m s) := by
  cases s with
  | linear =>
      exact centralizer_pCore_le_of_radical
        (linear_parabolic_le_radical_normalizer m) (linear_intrinsicRadical_centralizer_le hm)
  | suzuki =>
      exact centralizer_pCore_le_of_radical
        (suzuki_parabolic_le_radical_normalizer m) (suzuki_intrinsicRadical_centralizer_le hm)

private theorem units_three_free (m : ℕ) : ¬ 3 ∣ Nat.card (CoefficientField m)ˣ := by
  rw [Nat.card_units, field_card]
  have hfour : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using
      (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod, hfour]
  have hsub : (2 ^ (2 * m + 1) - 1) % 3 = 1 := by
    generalize 2 ^ (2 * m + 1) = q at hq ⊢
    omega
  intro hd
  have hz := Nat.dvd_iff_mod_eq_zero.mp hd
  omega

/-- The Suzuki parabolic has three-free order even with its complementary torus. -/
theorem suzuki_parabolic_three_free {m : ℕ} (hm : 1 ≤ m) :
    ¬ 3 ∣ Nat.card (parabolic m .suzuki) := by
  let f := suzukiProjection hm
  have ht : ¬ 3 ∣ Nat.card
      (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (CoefficientField m)ˣ) := by
    rw [Nat.card_prod]
    exact fun hd => (Nat.prime_three.dvd_mul.mp hd).elim
      (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm)
      (units_three_free m)
  intro hd
  rw [← f.ker.card_mul_index, index_ker] at hd
  rcases Nat.prime_three.dvd_mul.mp hd with hk3 | hr3
  · obtain ⟨n, hn⟩ := (suzukiProjection_ker_isPGroup hm).exists_card_eq
    change 3 ∣ Nat.card (suzukiProjection hm).ker at hk3
    rw [hn] at hk3
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hk3)
  · exact ht (hr3.trans f.range.card_subgroup_dvd_card)

namespace CoreActionRigidity
open LargeLocalSeeds

/-- The actual matrix-preserving inclusion of a canonical seed in its full parabolic. -/
@[expose] def seedInclusion (m : ℕ) (s : Side) :
    standardSeed (canonicalLocalBlockInput m) s →* parabolic m s where
  toFun x := ⟨(canonicalLocalBlockInput m).modelEquiv x.val,
    seed_map_le_parabolic _ s (mem_map_of_mem _ x.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The inclusion preserves the actual ambient Ree element. -/
@[simp] theorem seedInclusion_coe (m : ℕ) (s : Side)
    (x : standardSeed (canonicalLocalBlockInput m) s) :
    (seedInclusion m s x : Model m) = (canonicalLocalBlockInput m).modelEquiv x.val := rfl

theorem seedInclusion_injective (m : ℕ) (s : Side) :
    Function.Injective (seedInclusion m s) := by
  intro x y h
  exact Subtype.ext ((canonicalLocalBlockInput m).modelEquiv.injective
    (congrArg Subtype.val h))

/-- The seed's actual two-core becomes precisely the full parabolic's root radical. -/
theorem linear_seedCore_map {m : ℕ} (hm : 1 ≤ m) :
    (pCore 2 (standardSeed (canonicalLocalBlockInput m) .linear)).map
      (seedInclusion m .linear) = intrinsicRadical m .linear := by
  apply map_injective (parabolic m .linear).subtype_injective
  rw [intrinsicRadical_map, map_map]
  change (pCore 2 (standardSeed (canonicalLocalBlockInput m) .linear)).map
    ((canonicalLocalBlockInput m).modelEquiv.toMonoidHom.comp
      (standardSeed (canonicalLocalBlockInput m) .linear).subtype) = _
  rw [← seedRadical_linear_eq_twoCore hm, ← map_map, seedRadical_map,
    standardRadical_map_eq]

/-- The perfect seed as a subgroup of the full parabolic. -/
def linearSeed (m : ℕ) : Subgroup (parabolic m .linear) := (seedInclusion m .linear).range

def linearSeedEquiv (m : ℕ) :
    standardSeed (canonicalLocalBlockInput m) .linear ≃* linearSeed m :=
  MonoidHom.ofInjective (seedInclusion_injective m .linear)

theorem linearSeed_perfect {m : ℕ} (hm : 1 ≤ m) : Group.IsPerfect (linearSeed m) := by
  let := LargeLocalSeeds.linearSeed_perfect hm (canonicalLocalBlockInput m)
  exact Group.IsPerfect.ofSurjective (f := (linearSeedEquiv m).toMonoidHom)
    (linearSeedEquiv m).surjective

theorem intrinsicRadical_le_linearSeed {m : ℕ} (hm : 1 ≤ m) :
    intrinsicRadical m .linear ≤ linearSeed m := by
  rw [← linear_seedCore_map hm]
  rintro x ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

/-- The nontrivial third commutator survives the injective seed inclusion. -/
theorem linear_seed_iterated_commutator_ne_bot {m : ℕ} (hm : 1 ≤ m) :
    ⁅⁅intrinsicRadical m .linear, linearSeed m⁆, intrinsicRadical m .linear⁆ ≠ ⊥ := by
  have h := linearCore_iterated_commutator_ne_bot hm (canonicalLocalBlockInput m)
  intro hz
  apply h
  apply (map_eq_bot_iff_of_injective _ (seedInclusion_injective m .linear)).mp
  simpa only [map_commutator, linear_seedCore_map hm, ← MonoidHom.range_eq_map,
    linearSeed] using hz

end CoreActionRigidity
end ReeF4.ConverseParabolics
