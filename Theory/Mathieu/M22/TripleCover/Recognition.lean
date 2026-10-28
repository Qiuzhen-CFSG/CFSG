module

public import Theory.Mathieu.M22.TripleCover
public import Theory.GroupTheory.PerfectCentralCoverPrimeKernel
public import Theory.GroupTheory.PerfectCentralCoverSylowNine

/-!
# Recognition of the triple Mathieu cover

A genuine triple cover is mapped onto the native M₂₂ by its supplied
central-quotient isomorphism. Its projection kernel is exactly its center.
Every Sylow three-subgroup of M₂₂ has order nine, so the general central-cover
kernel bound excludes nine from the order of the universal cover's kernel.
The prime-kernel comparison therefore identifies every genuine triple cover
with the published binary matrix carrier.

Only this three-primary bound is needed; no full multiplier calculation or
legacy split cover model is used.

Source: Aschbacher–Smith H.12, printed pp.393–394, with the covering
convention of I.1.1, printed p.407.
-/

namespace Sporadic.Mathieu.M22TripleCover

public section

open PerfectCentralCovering Theory.GroupTheory

/-- The central covering specified by an actual central-quotient marking. -/
@[expose] noncomputable def coverOfCentralQuotientEquiv
    {L : Type*} [Group L] [IsQuasisimple L]
    (e : (L ⧸ Subgroup.center L) ≃* M22) : Cover L M22 where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

@[simp] theorem coverOfCentralQuotientEquiv_ker
    {L : Type*} [Group L] [IsQuasisimple L]
    (e : (L ⧸ Subgroup.center L) ≃* M22) :
    (coverOfCentralQuotientEquiv e).toMonoidHom.ker = Subgroup.center L := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- The Sylow three-subgroups of the native M₂₂ have order nine. -/
theorem m22_sylow_three_card (P : Sylow 3 M22) : Nat.card P = 9 := by
  rw [P.card_eq_multiplicity, m22_order]
  decide +kernel

/-- The three-primary part of the actual universal-cover kernel has order at most three. -/
theorem not_nine_dvd_universal_kernel :
    ¬ 9 ∣ Nat.card (universalProjection M22).ker := by
  let g := coverOfCentralQuotientEquiv centralQuotientEquiv
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective g.surjective
  let P : Sylow 3 M22 := Classical.choice inferInstance
  exact (universalCover M22).not_nine_dvd_card_kernel_of_sylow_nine
    P (m22_sylow_three_card P)

/-- Recognition reduced to the three-primary universal-kernel bound.
The additional arithmetic premise must be discharged for unconditional recognition. -/
theorem nonempty_mulEquiv_of_not_nine_dvd_universal_kernel
    (hbound : ¬ 9 ∣ Nat.card (universalProjection M22).ker)
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hcenter : Nat.card (Subgroup.center L) = 3)
    (hquotient : Nonempty ((L ⧸ Subgroup.center L) ≃* M22)) :
    Nonempty (L ≃* M22TripleCover) := by
  obtain ⟨e⟩ := hquotient
  let f := coverOfCentralQuotientEquiv e
  let g := coverOfCentralQuotientEquiv centralQuotientEquiv
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective g.surjective
  apply f.nonempty_mulEquiv_of_prime_kernel g (p := 3) (by decide)
  · exact hbound
  · simpa only [f, coverOfCentralQuotientEquiv_ker] using hcenter
  · simpa only [g, coverOfCentralQuotientEquiv_ker] using center_card

/-- Every finite quasisimple group with center of order three and central quotient
M₂₂ is isomorphic to the concrete triple Mathieu cover. -/
theorem nonempty_mulEquiv
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hcenter : Nat.card (Subgroup.center L) = 3)
    (hquotient : Nonempty ((L ⧸ Subgroup.center L) ≃* M22)) :
    Nonempty (L ≃* M22TripleCover) :=
  nonempty_mulEquiv_of_not_nine_dvd_universal_kernel
    not_nine_dvd_universal_kernel hcenter hquotient

end
end Sporadic.Mathieu.M22TripleCover
