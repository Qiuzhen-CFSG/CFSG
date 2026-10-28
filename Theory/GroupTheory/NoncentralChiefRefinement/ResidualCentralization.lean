module
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.ChiefSurvival
public import Theory.GroupAction.NormalPChiefSeries

/-!
# Central chief factors of a residual-centralized normal two-subgroup

A noncentral binary chief section remains noncentral when restricted to the
two-residual. If that residual centralizes the normal two-subgroup containing
the section, the restricted action is trivial, a contradiction. Thus every
actual chief series on the subgroup consists of central factors and its
noncentral count is zero.

Source application: the last step of Niles (1979), Lemma 7.3, converting the
centralizer supplement into the central-chief conclusion used in Theorem 7.2.
-/

public section
open Subgroup
open scoped commutatorElement
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

theorem SeriesOn.central_of_residual_centralizes
    {U : Subgroup H} [U.Normal] (s : SeriesOn U) (hU : IsPGroup 2 U)
    (hR : pResidual 2 H ≤ centralizer (U : Set H)) : ∀ i, s.Central i := by
  intro i
  by_contra hn
  have hp : IsPGroup 2 (s.Factor i) := (hU.to_le (s.upper_le i)).to_quotient _
  have hr := isNoncentralTwo_restrict_pResidual (s.lower i) (s.upper i)
    (s.series.step i) ⟨hp, hn⟩
  apply hr.2
  rw [isCentral_iff_commutator_le, Subgroup.commutator_le]
  intro x _ y hy
  have hxy : Commute x y := Subtype.ext ((hR x.property) y (s.upper_le i hy)).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy.eq]
  exact one_mem _

/-- A residual-centralized normal two-subgroup contributes no noncentral chief factors. -/
theorem SeriesOn.noncentralCount_eq_zero_of_residual_centralizes
    {U : Subgroup H} [U.Normal] (s : SeriesOn U) (hU : IsPGroup 2 U)
    (hR : pResidual 2 H ≤ centralizer (U : Set H)) : s.noncentralCount = 0 :=
  s.noncentralCount_eq_zero_iff.mpr (s.central_of_residual_centralizes hU hR)

end NoncentralChiefRefinement
