module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalPresentation
public import Theory.Mathieu.SchurMultipliers
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# A double-order bound suffices for the marked native comparison

The images of the two presentation generators in the abelianization have
orders dividing two and three. Their product has orders dividing six and
23, so both images are trivial: the seven-relator group is perfect.
A finite bound twice the native order makes the kernel have order at most
two, hence central. The proved trivial multiplier of the native Witt-design
M24 then kills this kernel. This relaxes the numerical bound without assuming
presentation faithfulness, and is consumed by `FourRelators.Source`.

Sources: John Bray, ATLAS M24G1-P1; Aschbacher–Smith I.1.3, printed p.407,
for the already proved native multiplier calculation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
open OrderBound Sporadic.Mathieu

/-- The literal seven-relator presentation is perfect. -/
theorem universal_perfect : Group.IsPerfect UniversalGroup := by
  let f : UniversalGroup →* Abelianization UniversalGroup := Abelianization.of
  let x := f (generator 0)
  let y := f (generator 1)
  have hx : x ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg f (show generator 0 ^ 2 = 1 from generator_relations 0)
  have hy : y ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg f (show generator 1 ^ 3 = 1 from generator_relations 1)
  have hxy : (y * x) ^ 23 = 1 := by
    simpa only [map_pow, map_mul, map_one] using congrArg f
      (show (generator 1 * generator 0) ^ 23 = 1 from generator_relations 2)
  have hsix : (y * x) ^ 6 = 1 := by
    rw [mul_pow, show 6 = 3 * 2 from rfl, pow_mul, hy, one_pow,
      one_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hx, one_pow]
  have hone : y * x = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hxy, hsix⟩
    simpa using h
  have hyx : y = x⁻¹ := mul_eq_one_iff_eq_inv.mp hone
  have hxthree : x ^ 3 = 1 := by simpa [hyx] using hy
  have hxone : x = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hx, hxthree⟩
    simpa using h
  have hyone : y = 1 := by simp [hyx, hxone]
  refine ⟨top_unique ?_⟩
  rw [← PresentedGroup.closure_range_of relators]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [← Abelianization.ker_of UniversalGroup]
  change f (PresentedGroup.of i) = 1
  fin_cases i
  · exact hxone
  · exact hyone

/-- The actual marked carrier map is injective under the relaxed finite bound. -/
theorem toCarrier_injective_of_double_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 489646080) :
    Function.Injective toCarrier := by
  let : Finite UniversalGroup := h.1
  let : Group.IsPerfect UniversalGroup := universal_perfect
  have hc := toCarrier.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr toCarrier_surjective,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup M24) ≃* M24).toEquiv,
    m24_order] at hc
  have hk : Nat.card toCarrier.ker ≤ 2 := by omega
  have hz : toCarrier.ker ≤ Subgroup.center UniversalGroup := by
    by_cases he : Nat.card toCarrier.ker = 2
    · exact Subgroup.central_of_normal_card_two _ he
    · have ho : Nat.card toCarrier.ker = 1 := by
        have hp : 0 < Nat.card toCarrier.ker := Nat.card_pos
        exact (show ∀ n : ℕ, n ≤ 2 → n ≠ 2 → 0 < n → n = 1 by omega) _ hk he hp
      rw [Subgroup.card_eq_one.mp ho]
      exact bot_le
  let c : PerfectCentralCovering.Cover UniversalGroup M24 :=
    { toMonoidHom := toCarrier
      surjective := toCarrier_surjective
      isPerfect := universal_perfect
      ker_le_center := hz }
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (Sporadic.Mathieu.SchurMultipliers.m24_cover_kernel_eq_bot c)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
