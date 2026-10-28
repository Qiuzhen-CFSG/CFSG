module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank

/-!
# Excluding a rank-two perfect subgroup from a linear parabolic

The literal projective parabolic residual is its affine vector or covector
stabilizer. Its two-core quotient is the actual SL₂ over the coefficient
field, whose odd Sylow subgroups are cyclic. Thus every perfect subgroup
of a parabolic has odd-prime rank at most one. Combining this with the
proved full-Sylow overgroup geometry excludes a proper Sylow overgroup
containing a perfect subgroup of odd-prime rank two.

Source: Aschbacher–Smith 2.5.6, printed p.554, binary PSL₃ target case.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.PerfectSubgroups
variable (F : Type*) [Field F] [Finite F]

/-- The literal projective point-parabolic residual is the affine point local. -/
theorem pointParabolic_residual (hcard : 4 ≤ Nat.card F) :
    (solvableResidual (pointParabolic F)).map (pointParabolic F).subtype = pointLocal F := by
  let f := (projection F).subgroupMap (pointParabolicSL F)
  have hf : Function.Surjective f := (projection F).subgroupMap_surjective _
  have hm := congrArg
    (fun A : Subgroup ((pointParabolicSL F).map (projection F)) =>
      A.map ((pointParabolicSL F).map (projection F)).subtype)
    (map_solvableResidual_eq f hf)
  rw [Subgroup.map_map] at hm
  have he : ((pointParabolicSL F).map (projection F)).subtype.comp f =
      (projection F).comp (pointParabolicSL F).subtype := rfl
  rw [he, ← Subgroup.map_map, pointParabolicSL_residual F hcard] at hm
  exact hm.symm

/-- The literal projective line-parabolic residual is the affine line local. -/
theorem lineParabolic_residual (hcard : 4 ≤ Nat.card F) :
    (solvableResidual (lineParabolic F)).map (lineParabolic F).subtype = lineLocal F := by
  let f := (projection F).subgroupMap (lineParabolicSL F)
  have hf : Function.Surjective f := (projection F).subgroupMap_surjective _
  have hm := congrArg
    (fun A : Subgroup ((lineParabolicSL F).map (projection F)) =>
      A.map ((lineParabolicSL F).map (projection F)).subtype)
    (map_solvableResidual_eq f hf)
  rw [Subgroup.map_map] at hm
  have he : ((lineParabolicSL F).map (projection F)).subtype.comp f =
      (projection F).comp (lineParabolicSL F).subtype := rfl
  rw [he, ← Subgroup.map_map, lineParabolicSL_residual F hcard] at hm
  exact hm.symm

variable [CharP F 2] {p : ℕ} [Fact p.Prime]

/-- The two-core quotient of the first affine local loses no odd prime rank. -/
theorem pointLocal_odd_primeRank_le_one (ho : Odd p) : primeRank p (pointLocal F) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (pointLocal F)) pCore_isPGroup,
    primeRank_congr p (pointLocalCoreQuotientEquiv F)]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

/-- The same rank bound for the second affine local. -/
theorem lineLocal_odd_primeRank_le_one (ho : Odd p) : primeRank p (lineLocal F) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (lineLocal F)) pCore_isPGroup,
    primeRank_congr p (lineLocalCoreQuotientEquiv F)]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

/-- A perfect odd-rank-two subgroup cannot lie in either actual projective parabolic. -/
theorem no_perfect_odd_rank_two_in_parabolic {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] (ho : Odd p) (hr : 2 ≤ primeRank p K) (hcard : 4 ≤ Nat.card F)
    (f : K →* PSL(3,F)) (hf : Function.Injective f)
    (hlocal : f.range ≤ pointParabolic F ∨ f.range ≤ lineParabolic F) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hlocal with hlocal | hlocal
  · have hh : f.range ≤ pointLocal F := by
      rw [← pointParabolic_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hlocal
    let g := f.codRestrict (pointLocal F) (fun x => hh ⟨x,rfl⟩)
    have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
    have h₁ := primeRank_le_of_injective p g hg
    have h₂ := pointLocal_odd_primeRank_le_one F ho
    omega
  · have hh : f.range ≤ lineLocal F := by
      rw [← lineParabolic_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hlocal
    let g := f.codRestrict (lineLocal F) (fun x => hh ⟨x,rfl⟩)
    have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
    have h₁ := primeRank_le_of_injective p g hg
    have h₂ := lineLocal_odd_primeRank_le_one F ho
    omega

/-- A full-Sylow overgroup containing the actual perfect rank-two subgroup is the whole PSL₃. -/
theorem perfect_odd_rank_two_sylow_overgroup_eq_top {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] (ho : Odd p) (hr : 2 ≤ primeRank p K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (D : Subgroup PSL(3,F)) (hPD : (P : Subgroup PSL(3,F)) ≤ D)
    (f : K →* PSL(3,F)) (hf : Function.Injective f) (hKD : f.range ≤ D) : D = ⊤ := by
  by_contra hD
  obtain ⟨g,hg⟩ := UnipotentOvergroups.proper_sylow_overgroup_parabolic_cover F (n := n)
    (by omega) hF P D hPD hD
  let t : K →* PSL(3,F) := (MulAut.conj g).toMonoidHom.comp f
  have ht : Function.Injective t := (MulAut.conj g).injective.comp hf
  have htr : t.range ≤ D.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hKD
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  exact no_perfect_odd_rank_two_in_parabolic F ho hr hcard t ht
    (hg.imp htr.trans htr.trans)

end Matrix.PSL3.LinearThree.PerfectSubgroups
