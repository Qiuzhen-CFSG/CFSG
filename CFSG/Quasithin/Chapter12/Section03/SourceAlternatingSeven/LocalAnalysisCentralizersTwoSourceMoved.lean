module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceConclusion

/-!+# A weight-four vector in the literal moved A₅ module

Move the support pair to the first two letters, choose the standard disjoint
four-letter word, and transport back. The point-residual action identifies
words vanishing on the support pair with the actual subgroup [V,C_L(e)∞].
Thus multiplying e by this moved vector gives a weight-six point in V.

Source: Aschbacher--Smith, Lemma 12.3.8, printed p.810. This is the vector
used both in the second-A₇-component contradiction and in the final
quotient-centralizer argument. It uses no ambient centralizer bound.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The source vector has weight four, lies in the original moved subgroup,
and gives a weight-six point when multiplied by the marked point. -/
theorem exists_five_moved_weight_four :
    ∃ w : V, (w : G) ∈ ⁅V,P.five⁆ ∧
      weight (E.coordinates w).toAdd.val = 4 ∧
      weight (E.coordinates (P.two * w)).toAdd.val = 6 := by
  obtain ⟨a,ha⟩ := exists_alternating_of_weight_eq (E.coordinates P.two).toAdd e2
    (P.two_weight.trans representative_weights.1.symm)
  let y := evenRepresentation a.val⁻¹ e4
  let w : V := E.coordinates.symm (Multiplicative.ofAdd y)
  have hw : (E.coordinates w).toAdd = y := by
    exact congrArg Multiplicative.toAdd (E.coordinates.apply_symm_apply _)
  have hy : evenRepresentation a.val y = e4 := by
    change evenRepresentation a.val (evenRepresentation a.val⁻¹ e4) = e4
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  have hz : ∀ i ∈ WeightTwoGeometry.support (E.coordinates P.two).toAdd,
      (E.coordinates w).toAdd.val i = 0 := by
    intro i hi
    have hpair : e2.val (a.val i) ≠ 0 := by
      have hh := congrArg (fun x : EvenWord => x.val (a.val i)) ha
      simp only [evenRepresentation_apply, Equiv.symm_apply_apply] at hh
      rw [← hh]
      exact (Finset.mem_filter.mp hi).2
    have hzero : e4.val (a.val i) = 0 :=
      (by decide : ∀ j : Fin 7, e2.val j ≠ 0 → e4.val j = 0) _ hpair
    rw [hw]
    exact hzero
  refine ⟨w,P.support_zero_mem_five_moved w hz,?_,?_⟩
  · rw [hw]
    exact (weight_evenRepresentation a.val⁻¹ e4).trans representative_weights.2.1
  · have he : evenRepresentation a.val (E.coordinates (P.two * w)).toAdd = e6 := by
      rw [map_mul, toAdd_mul, map_add, ha, hw, hy]
      decide
    exact (weight_evenRepresentation a.val _).symm.trans
      ((congrArg (fun x : EvenWord => weight x.val) he).trans representative_weights.2.2)

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
