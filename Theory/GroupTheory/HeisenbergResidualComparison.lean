module
public import Theory.SpecificGroups.HeisenbergPrime.TernaryOuterAction
public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Comparing the full two-residual with a normal Heisenberg subgroup

Conjugation on a normal Heisenberg group of order 27, followed by its
actual action on the noncentral plane, has kernel R C_D(R). When the
centralizer is contained in R, the kernel is exactly R. Restricting to
O²(D) therefore identifies its quotient by R with a two-perfect subgroup
of GL₂(3): it is trivial, cubic, or the actual determinant kernel SL₂(3).

This comparison retains the inner automorphisms and makes no assertion
that the extension splits. Source application: Aschbacher–Smith 14.7.15(3)
and 14.7.27, printed pp.1047,1054, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix
namespace Subgroup
variable {D : Type*} [Group D]

/-- For a self-centralizing normal Heisenberg subgroup, the literal
noncentral-plane action has kernel precisely that subgroup. -/
theorem heisenberg_outerAction_ker
    (R : Subgroup D) [R.Normal] (e : R ≃* HeisenbergPrime 3)
    (hc : centralizer (R : Set D) ≤ R) :
    ((HeisenbergPrime.TernaryOuterAction.markedAction e).comp
      (MulAut.conjNormal : D →* MulAut R)).ker = R := by
  rw [←MonoidHom.comap_ker,HeisenbergPrime.TernaryOuterAction.markedAction_ker,
    MulAut.conjNormal_comap_innerSubgroup,sup_eq_left.mpr hc]

/-- The full two-residual modulo a normal self-centralizing Heisenberg
subgroup is trivial, cubic, or isomorphic to SL₂(3). -/
theorem heisenberg_twoResidual_comparison [Finite D]
    (R : Subgroup D) [R.Normal] (e : R ≃* HeisenbergPrime 3)
    (hc : centralizer (R : Set D) ≤ R) (hR : R ≤ pResidual 2 D) :
    R = pResidual 2 D ∨
      Nat.card ((pResidual 2 D) ⧸ R.subgroupOf (pResidual 2 D)) = 3 ∨
      Nonempty (((pResidual 2 D) ⧸ R.subgroupOf (pResidual 2 D)) ≃*
        SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp
    (MulAut.conjNormal : D →* MulAut R)
  have hk : f.ker = R := heisenberg_outerAction_ker R e hc
  let a := f.comp (pResidual 2 D).subtype
  have ha : a.ker = R.subgroupOf (pResidual 2 D) := by
    rw [←MonoidHom.comap_ker,hk]
    rfl
  let eQ := (QuotientGroup.quotientMulEquivOfEq ha.symm).trans
    (QuotientGroup.quotientKerEquivRange a)
  by_cases hb : a.range = ⊥
  · left
    apply le_antisymm hR
    intro x hx
    rw [←hk]
    exact mem_bot.mp (hb ▸ (show a ⟨x,hx⟩ ∈ a.range from ⟨⟨x,hx⟩,rfl⟩))
  · right
    rcases GeneralLinearGroup.three_twoPerfect_subgroup a.range
      ((isPPerfect_pResidual 2).of_surjective a.rangeRestrict a.rangeRestrict_surjective) hb
      with h | h
    · left
      exact (Nat.card_congr eQ.toEquiv).trans h
    · right
      exact ⟨eQ.trans ((MulEquiv.subgroupCongr h).trans
        GeneralLinearGroup.threeSpecialLinearEquiv)⟩
end Subgroup
