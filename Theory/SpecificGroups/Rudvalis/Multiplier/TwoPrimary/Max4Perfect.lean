module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Comparison
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Tactic.Group

/-!
# Perfectness of the literal ATLAS max4 subgroup

Let x and y be the two defining max4 generators. The concrete relations
x² = y³ = (xy)¹⁴ = 1 force y to vanish in the abelianization. A further
order-three word containing an odd number of copies of x forces x to
vanish too. These relations are checked on the certified five-point base
of the actual degree-4060 Rudvalis action; no presentation completeness
claim is used.

This supplies the perfect local subgroup required in the restriction
argument for Aschbacher--Smith I.1.3(1), printed p.407. The ATLAS generator
words and their attribution are in `SylowOvergroups.Definitions`.
-/

namespace Rudvalis.Multiplier.TwoPrimary
open SylowOvergroups
private def oddWord {G : Type*} [Group G] (x y : G) : G :=
  (x * y ^ 2) ^ 2 * (x * y) ^ 2 * (x * y ^ 2) * (x * y) *
    (x * y ^ 2) ^ 4 * (x * y)

private def second : max4 := ⟨max4Generators.2, Subgroup.subset_closure (by simp)⟩

/-- The marked first max4 generator squares to the identity. -/
public theorem max4First_sq : max4First ^ 2 = 1 := by
  apply Subtype.ext
  apply eq_of_smul_first_five
  intro i
  change ((modelSubgroup.subtype max4Generators.1) ^ 2) (i.castLE (by decide)) = i.castLE (by decide)
  rw [← LocalCardinality.Max4.generator0_eq]
  revert i
  decide +kernel

private theorem second_cube : second ^ 3 = 1 := by
  apply Subtype.ext
  apply eq_of_smul_first_five
  intro i
  change ((modelSubgroup.subtype max4Generators.2) ^ 3) (i.castLE (by decide)) = i.castLE (by decide)
  rw [← LocalCardinality.Max4.generator1_eq]
  revert i
  decide +kernel

private theorem product_fourteenth : (max4First * second) ^ 14 = 1 := by
  apply Subtype.ext
  apply eq_of_smul_first_five
  intro i
  change ((modelSubgroup.subtype max4Generators.1 * modelSubgroup.subtype max4Generators.2) ^ 14)
    (i.castLE (by decide)) = i.castLE (by decide)
  rw [← LocalCardinality.Max4.generator0_eq, ← LocalCardinality.Max4.generator1_eq]
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
private theorem word_cube : oddWord max4First second ^ 3 = 1 := by
  apply Subtype.ext
  apply eq_of_smul_first_five
  intro i
  change (oddWord (modelSubgroup.subtype max4Generators.1) (modelSubgroup.subtype max4Generators.2) ^ 3)
    (i.castLE (by decide)) = i.castLE (by decide)
  rw [← LocalCardinality.Max4.generator0_eq, ← LocalCardinality.Max4.generator1_eq]
  revert i
  decide +kernel

private theorem eq_top_of_first_second (H : Subgroup max4) (hx : max4First ∈ H) (hy : second ∈ H) :
    H = ⊤ := by
  have hle : max4 ≤ H.map max4.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact ⟨max4First, hx, rfl⟩
    · exact ⟨second, hy, rfl⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

/-- The actual word-generated max4 subgroup is perfect. -/
public theorem max4_isPerfect : Group.IsPerfect max4 := by
  let q : max4 →* Abelianization max4 := Abelianization.of
  have hx : q max4First ^ 2 = 1 := by rw [← map_pow, max4First_sq, map_one]
  have hy : q second ^ 3 = 1 := by rw [← map_pow, second_cube, map_one]
  have hxy : (q max4First * q second) ^ 14 = 1 := by
    rw [← map_mul, ← map_pow, product_fourteenth, map_one]
  have hxy6 : (q max4First * q second) ^ 6 = 1 := by
    rw [mul_pow, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hx, one_pow,
      show q second ^ (2 * 3) = (q second ^ 3) ^ 2 by group, hy]
    simp
  have hxy2 : (q max4First * q second) ^ 2 = 1 := by
    have he : (q max4First * q second) ^ 14 = (q max4First * q second) ^ 2 := by
      calc
        _ = ((q max4First * q second) ^ 6) ^ 2 * (q max4First * q second) ^ 2 := by group
        _ = (q max4First * q second) ^ 2 := by rw [hxy6]; simp
    exact he.symm.trans hxy
  have hy2 : q second ^ 2 = 1 := by simpa only [mul_pow, hx, one_mul] using hxy2
  have hy1 : q second = 1 := by
    have he : q second ^ 3 = q second := by rw [pow_succ, hy2, one_mul]
    exact he.symm.trans hy
  have hw : oddWord (q max4First) (q second) ^ 3 = 1 := by
    simpa only [oddWord, map_mul, map_pow, map_one] using congrArg q word_cube
  have hword : oddWord (q max4First) (q second) ^ 3 = q max4First := by
    simp only [oddWord, hy1, one_pow, mul_one, hx]
    calc
      _ = (q max4First ^ 2) ^ 10 * q max4First := by group
      _ = q max4First := by rw [hx]; simp
  have hx1 : q max4First = 1 := hword.symm.trans hw
  refine ⟨eq_top_of_first_second _ ?_ ?_⟩
  · rw [← Abelianization.ker_of]
    exact hx1
  · rw [← Abelianization.ker_of]
    exact hy1

end Rudvalis.Multiplier.TwoPrimary
