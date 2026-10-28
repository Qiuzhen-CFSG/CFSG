module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.ElementaryForm
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Assembly

/-!
# First-centralizer reduction for the native outer-half symmetry

Conjugation by an element of the checked first-centralizer census fixes the
marked involution `a`.  Hence both orientations of `InnerRelated` are constant
on each of the eleven certified local conjugacy classes.  The existing
square-one census then reduces symmetry for the whole first centralizer to the
eleven literal representative comparisons.

This is the finite native reduction used by the recovered Kleidman--Wilson
four-group argument.  It does not assert the missing comparisons, and it does
not package any radical coverage or quotient classification premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Both orientations of `InnerRelated` are transported by a conjugacy in the
literal first-centralizer census. -/
theorem innerRelated_first_class_iff {u v : H} (huv : IsConj u v) :
    (InnerRelated Janko4.a (eH u) ↔ InnerRelated Janko4.a (eH v)) ∧
      (InnerRelated (eH u) Janko4.a ↔ InnerRelated (eH v) Janko4.a) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp huv
  have ha : (MulAut.conj (eH g)) Janko4.a = Janko4.a := by
    have hc := (eH_commute_z g).eq
    change eH g * Janko4.a = Janko4.a * eH g at hc
    change eH g * Janko4.a * (eH g)⁻¹ = Janko4.a
    rw [hc, mul_inv_cancel_right]
  have hv : (MulAut.conj (eH g)) (eH u) = eH v := by
    simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg eH hg
  constructor
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv] using
      (innerRelated_equiv (MulAut.conj (eH g)) Janko4.a (eH u)).symm
  · simpa only [MulEquiv.coe_toMonoidHom, ha, hv] using
      (innerRelated_equiv (MulAut.conj (eH g)) (eH u) Janko4.a).symm

/-- Once the eleven checked representatives have both residual-membership
orientations, the whole first-centralizer census has commuting-involution
symmetry.  The representative premise is the exact remaining finite native
comparison, with no quotient or coverage conclusion bundled into it. -/
theorem first_centralizer_symmetry_of_representatives
    (hH : Nat.card H ≤ 21799895040)
    (hpair : ∀ i : Fin 11,
      InnerRelated Janko4.a (eH (representative i)) ↔
        InnerRelated (eH (representative i)) Janko4.a)
    (u : H) (hu : u ^ 2 = 1) :
    InnerRelated Janko4.a (eH u) ↔ InnerRelated (eH u) Janko4.a := by
  obtain ⟨i, hi⟩ := square_one_coverage hH u hu
  have hc := innerRelated_first_class_iff hi
  rw [← hc.1, hpair i, hc.2]

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
