module
public import ABG.ChapterII.Section1.WreathedOuterFour
public import ABG.ChapterII.Section1.WreathedMaximalQuaternion
public import Theory.GroupTheory.SpecificGroups.QuaternionContainment

/-!
# The unique largest quaternion subgroup in a wreathed group

Every generalized quaternion subgroup of a chosen wreathed presentation lies
in Y = ⟨r,d⟩. Since Y has order 2^(n+1), any generalized quaternion subgroup
of that order equals Y. The presentation retains the essential height bound
n ≥ 2 and the exact ambient cardinality.

The base subgroup U is abelian, and the square of any element outside U is
central. The general quaternion containment theorem therefore reduces the
claim to outside elements of order four. WreathedOuterFour places every such
element in Y by its bounded coordinates. WreathedMaximalQuaternion supplies
the cardinality for the final equality.

This is the uniqueness clause of ABG Chapter II §1 Lemma 2(v), article p.9
in `refs/latex/alperin-brauer-gorenstein.tex`.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- Every generalized quaternion subgroup lies in the designated subgroup Y. -/
public theorem quaternion_le_Y (Q : Subgroup S)
    (hQ : ABG.IsGeneralizedQuaternionGroup Q) : Q ≤ P.Y := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hQ
  have hm2 : 2 ≤ 2^m := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
  exact QuaternionGroup.subgroup_le_of_outer_order_four P.U P.Y Q
    (fun _ ha _ hb => P.commute_of_mem_U ha hb)
    (fun _ ha b => P.outer_square_commute ha b)
    (fun _ ha ho => P.outer_order_four_mem_Y ha ho) hm2 e

/-- The designated quaternion subgroup is the only one of order 2^(n+1). -/
public theorem quaternion_unique (Q : Subgroup S)
    (hQ : ABG.IsGeneralizedQuaternionGroup Q)
    (hcardQ : Nat.card Q = 2 ^ (n + 1)) : Q = P.Y := by
  have hcardY := P.quaternion_subgroup.2.1
  let : Finite P.Y := Nat.finite_of_card_ne_zero (by rw [hcardY]; positivity)
  exact Subgroup.eq_of_le_of_card_ge (P.quaternion_le_Y Q hQ) (by rw [hcardY, hcardQ])

end ABG.Wreathed.Presentation
