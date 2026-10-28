module
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SymmetricFive.OuterFourIntersection

/-!
# An extraspecial plus core in a marked symmetric-five quotient

The center of Q8*Q8 lies in the kernel, so its quotient image is elementary.
An elementary subgroup of S5 has order at most four; an elementary kernel
in Q8*Q8 has order at most eight. Since the core has order32, both bounds
are attained. This gives the literal hyperplane kernel and outer-four
candidate used in Aschbacher–Smith 6.2.13, printed p688.
-/
public noncomputable section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

include d in
/-- Both elementary order bounds are forced to equality by the core order. -/
theorem symmetricFive_image (f : Q →* Equiv.Perm (Fin 5))
    (hZ : center Q ≤ f.ker) (hker : IsElementaryAbelian 2 f.ker) :
    IsElementaryAbelian 2 f.range ∧ Nat.card f.ker = 8 ∧ Nat.card f.range = 4 := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) := d.quotient_elementary
  have hZ' : center Q ≤ f.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using hZ
  let ff := QuotientGroup.lift (center Q) f.rangeRestrict hZ'
  have hff : Function.Surjective ff :=
    QuotientGroup.lift_surjective_of_surjective _ _ f.rangeRestrict_surjective _
  let hE : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective ff hff
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 f.range).exists_le_sylow
  have hr := Theory.SpecificGroups.SymmetricFive.OuterFourIntersection.elementary_card_le_four T f.range hT
  have hk := d.elementary_card_le_eight f.ker hker
  have hc := f.ker.card_mul_index
  rw [index_ker,d.card] at hc
  exact ⟨hE, by nlinarith, by nlinarith⟩
end Subgroup.QuaternionCentralProductData
