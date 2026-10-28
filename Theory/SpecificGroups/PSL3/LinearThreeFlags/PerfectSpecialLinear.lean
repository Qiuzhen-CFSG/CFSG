module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank

/-!
# Perfect subgroups of the special-linear three-space parabolics

The actual parabolic residual is its affine determinant-one local.
Its two-core quotient is SL₂, so every perfect subgroup has odd-prime
rank at most one. This retains the special-linear carrier, including
its possible odd center.

Source: Aschbacher–Smith C.2.7(g), pp.145–147, and 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.PerfectSubgroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem perfect_parabolicSL_rank {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hcard : 4 ≤ Nat.card F)
    (f : A →* SL(3,F)) (hf : Function.Injective f)
    (hp : f.range ≤ pointParabolicSL F ∨ f.range ≤ lineParabolicSL F) :
    primeRank p A ≤ 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hh : f.range ≤ pointLocalSL F := by
      rw [←pointParabolicSL_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (pointLocalSL F) (fun x => hh ⟨x,rfl⟩)
    have hr := Theory.GroupTheory.primeRank_le_of_injective p j
      (fun _ _ h => hf (congrArg Subtype.val h))
    have hl : primeRank p (pointLocalSL F) ≤ 1 := by
      rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (pointLocalSL F)) pCore_isPGroup,
        primeRank_equiv p (pointLocalSLCoreQuotientEquiv F)]
      exact Matrix.SL2.binary_odd_primeRank_le_one ho
    exact hr.trans hl
  · have hh : f.range ≤ lineLocalSL F := by
      rw [←lineParabolicSL_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (lineLocalSL F) (fun x => hh ⟨x,rfl⟩)
    have hr := Theory.GroupTheory.primeRank_le_of_injective p j
      (fun _ _ h => hf (congrArg Subtype.val h))
    have hl : primeRank p (lineLocalSL F) ≤ 1 := by
      rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (lineLocalSL F)) pCore_isPGroup,
        primeRank_equiv p (lineLocalSLCoreQuotientEquiv F)]
      exact Matrix.SL2.binary_odd_primeRank_le_one ho
    exact hr.trans hl
end Matrix.PSL3.LinearThree.PerfectSubgroups
