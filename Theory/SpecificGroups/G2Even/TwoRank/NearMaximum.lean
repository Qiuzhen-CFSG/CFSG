module

public import Theory.SpecificGroups.G2Even.TwoRank.OuterBound
public import Theory.GroupAction.SemidirectElementaryKernel


/-!
# Outer elementary G₂ actors below the near-maximal rank

The coefficient kernel lies in G₂ over the half-degree fixed field. Its
rank is at most 3m, so the whole outer actor has rank at most 3m+1,
strictly below 6m-1. This is the bound needed by the actual natural-module
degree 6n and the original actor inequality.

Source: Aschbacher–Smith G.9.3(10), G.11.7.
-/

public section
open Theory.GroupTheory
open scoped IsMulCommutative
namespace Atlas.G2.EvenTwoRank
open LieAutomorphismExtensions EvenFieldFixedResidual
open Theory.GroupTheory.SemidirectElementaryKernel
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- A nontrivial field projection forces rank strictly below 3n-1. -/
theorem outer_elementary_card_lt_near_maximum {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (Model F ⋊[fieldAction] (F ≃+* F)))
    (hE : IsElementaryAbelian 2 E)
    (z : E) (hz : z.1.right ≠ 1) : Nat.card E < 2 ^ (3 * n - 1) := by
  classical
  let := hE
  have hz2 : z.1 ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z.1 z.2
  have hs : orderOf z.1.right = 2 :=
    orderOf_eq_prime (congrArg SemidirectProduct.right hz2) hz
  have hg : z.1.left * fieldAction z.1.right z.1.left = 1 :=
    congrArg SemidirectProduct.left hz2
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  obtain ⟨c, hc⟩ := cocycle_eq_coboundary hq z.1.right hs z.1.left hg
  let d := coefficientFixedEquiv z.1.right
  obtain ⟨m, hm, hnm, hFm⟩ := fixedField_card z.1.right hs hF
  let f : E →* (F ≃+* F) := SemidirectProduct.rightHom.comp E.subtype
  let j : f.ker →* Model (fixedField z.1.right) :=
    d.toMonoidHom.comp (kernelFixed E z c hc)
  have hj : Function.Injective j := d.injective.comp (kernelFixed_injective E z c hc)
  let : IsElementaryAbelian 2 f.ker := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.1) }
  have he : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hk := (primeRank_le_iff_elementary_card_le _).mp
    (two_rank (fixedField z.1.right) hFm).le j.range he
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv] at hk
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : Nat.card f.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    exact he.exponent_dvd_p
  calc
    Nat.card E = Nat.card f.ker * Nat.card f.range := by
      rw [← f.ker.card_mul_index, Subgroup.index_ker]
    _ ≤ 2 ^ (3 * m) * 2 := Nat.mul_le_mul hk hr
    _ = 2 ^ (3 * m + 1) := by rw [pow_succ]
    _ < 2 ^ (3 * n - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
end Atlas.G2.EvenTwoRank

