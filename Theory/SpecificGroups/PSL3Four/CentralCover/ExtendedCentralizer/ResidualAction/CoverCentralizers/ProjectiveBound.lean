module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.Counting
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.ProjectiveBound.ResidualStability
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.NineExtension.Automorphisms

/-!
# Bounding the projective centralizer by its action on the residual

The actual projective centralizer preserves the faithfully projected E₉
residual. Its restriction image has order dividing |Aut(E₉)| = |GL₂(3)| = 48,
and its kernel embeds in the standard pointwise fixer of that same subgroup.
The matrix calculation in `ResidualAction.ProjectiveFixer` proves that this
pointwise fixer's order divides eighteen, so the projective centralizer's
order divides 864. The result applies to the original w and in particular to
the marked graph-field product, without any graph-field conjugacy assumption.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. The supplied residual model is used through its actual covering
projection, without replacing the marked graph and field involutions.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- Faithful projection identifies the restriction target with the supplied E₉. -/
theorem ProjectiveBound.action_range_card_dvd (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (ProjectiveBound.action d w).range ∣ 48 := by
  have he : projectedResidual d.cover w ≃* ElementaryNine :=
    ((residualProjectionEquiv d.cover w e).symm.trans (fixedResidualEquiv w).symm).trans e
  simpa only [NineExtension.automorphism_card he] using
    (ProjectiveBound.action d w).range.card_subgroup_dvd_card

/-- The projective centralizer order divides 48 times the pointwise-fixer order. -/
theorem projectiveCentralizer_card_dvd_fixer_mul_48 (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (projectiveCentralizer d w) ∣
      Nat.card (projectedResidualFixer d.cover w) * 48 := by
  rw [Nat.mul_comm (Nat.card (projectedResidualFixer d.cover w)) 48]
  rw [card_eq_card_quotient_mul_card_subgroup (ProjectiveBound.action d w).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (ProjectiveBound.action d w)).toEquiv]
  exact Nat.mul_dvd_mul (ProjectiveBound.action_range_card_dvd d w e)
    (ProjectiveBound.kernel_card_dvd_fixer d w)

/-- The independent matrix fixer calculation suffices for the requested bound.
Its explicit premise must be discharged before applying this as a source result. -/
theorem projectiveCentralizer_card_dvd_of_projectedFixer_card_dvd
    (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (hfix : Nat.card (projectedResidualFixer d.cover w) ∣ 18) :
    Nat.card (projectiveCentralizer d w) ∣ 864 :=
  (projectiveCentralizer_card_dvd_fixer_mul_48 d w e).trans
    (Nat.mul_dvd_mul_right hfix 48)

/-- The actual standard projective centralizer has order dividing 864 whenever
the intrinsic linear two-residual is the supplied E₉. -/
theorem projectiveCentralizer_card_dvd (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (projectiveCentralizer d w) ∣ 864 :=
  projectiveCentralizer_card_dvd_of_projectedFixer_card_dvd d w e
    (projectedResidualFixer_card_dvd d.cover w e)

/-- The projective centralizer bound for the original marked graph-field product.
The E₉ equivalence is the only model input beyond the given overgroup geometry. -/
theorem graphField_projectiveCentralizer_card_dvd (d : Overgroup L)
    (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    Nat.card (projectiveCentralizer d n.graphFieldI) ∣ 864 :=
  projectiveCentralizer_card_dvd d n.graphFieldI e

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
