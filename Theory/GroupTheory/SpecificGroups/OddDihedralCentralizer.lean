module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

/-!
# Centralizers of nontrivial two-subgroups in odd dihedral groups

When the rotation order is odd, the centralizer of a nontrivial two-subgroup
is a two-group. Cauchy's theorem supplies an involution in that subgroup.
Oddness excludes a nonidentity involution among the rotations, so this is a
reflection. Explicit dihedral multiplication and injectivity of doubling in
`ZMod order` show that its centralizer consists of itself and the identity.
Every element of the original subgroup's centralizer therefore squares to one.

This intrinsic dihedral calculation supports the kernel reduction in the first
paragraph of Stellmacher (8.5), journal p. 40: after transport to an odd dihedral
core quotient, a kernel centralizing a nontrivial two-subgroup is a two-group.
Normality and triviality of the quotient's two-core are separate inputs used by
the caller. Source: `refs/latex/stellmacher-n-group.tex` and the full paper scan.
-/

namespace DihedralGroup

private theorem commute_reflection_eq
    {order : ℕ} (hodd : Odd order) (index : ZMod order)
    (element : DihedralGroup order) (hcomm : Commute element (.sr index)) :
    element = 1 ∨ element = .sr index := by
  cases element with
  | r coordinate =>
      left
      have heq := DihedralGroup.sr.inj hcomm.eq
      have hzero : coordinate = 0 := by
        apply (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp
        linear_combination -heq
      simp [hzero]
  | sr coordinate =>
      right
      have heq := DihedralGroup.r.inj hcomm.eq
      have hzero : coordinate - index = 0 := by
        apply (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp
        linear_combination -heq
      rw [sub_eq_zero.mp hzero]

/-- In a dihedral group of odd rotation order, the centralizer of a nontrivial
two-subgroup is a two-group. -/
public theorem isPGroup_centralizer_of_nontrivial_two_subgroup
    {order : ℕ} (hodd : Odd order)
    (actor : Subgroup (DihedralGroup order))
    (hactor : IsPGroup 2 actor) (hne : actor ≠ ⊥) :
    IsPGroup 2 (Subgroup.centralizer (actor : Set (DihedralGroup order))) := by
  classical
  let : NeZero order := ⟨hodd.pos.ne'⟩
  let : Nontrivial actor := (Subgroup.nontrivial_iff_ne_bot actor).mpr hne
  obtain ⟨power, hpositive, hcard⟩ := hactor.nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card actor := by
    rw [hcard]
    exact dvd_pow_self 2 hpositive.ne'
  obtain ⟨reflection, hreflection⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  have horder : orderOf (reflection : DihedralGroup order) = 2 := by
    simpa using hreflection
  have hsquare : (reflection : DihedralGroup order) ^ 2 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one _
  have hnotone : (reflection : DihedralGroup order) ≠ 1 := by
    intro heq
    simp [heq] at horder
  obtain ⟨index, hindex⟩ : ∃ index, (reflection : DihedralGroup order) = .sr index := by
    cases helement : (reflection : DihedralGroup order) with
    | sr index => exact ⟨index, rfl⟩
    | r index =>
        have hzero : index = 0 := by
          apply (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp
          simpa [helement, pow_two, ← DihedralGroup.r_zero] using hsquare
        exact (hnotone (by simp [helement, hzero])).elim
  rw [isPGroup_iff_pow_pow_eq_one]
  intro element
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hcomm : Commute (element : DihedralGroup order) (.sr index) := by
    rw [← hindex]
    exact (Subgroup.mem_centralizer_iff.mp element.property reflection reflection.property).symm
  rcases commute_reflection_eq hodd index element hcomm with heq | heq
  · simp [heq]
  · simp [heq, pow_two]

end DihedralGroup
