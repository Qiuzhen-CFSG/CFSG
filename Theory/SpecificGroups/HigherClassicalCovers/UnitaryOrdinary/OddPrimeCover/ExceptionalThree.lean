module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Index
public import Theory.ElementaryAbelian.Join

/-!
# The exceptional odd kernel over PSU₄(3)

The completed cubic-defect root calculation splits the positive subgroup after
quotienting by two central elements of order dividing three. Its index is prime
to three, so transfer removes the three-part of the remaining covering kernel.
The independent nondefining calculation already makes every odd kernel a
three-group. Thus the whole kernel equals the elementary cubic defect subgroup
and has order dividing nine.

The arbitrary-form adapter retains the supplied central-quotient marking and
proves the actual center exponent and order bound. It does not assert that
partial central quotients are quasithin; that is a separate source step.

Source: Aschbacher–Smith I.1.4(5), printed p.408, and the exceptional unitary
branch of A.2.17; GLS3 §6.1.
-/

open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open UnitaryThreeExceptional.ThreePrimary

public theorem ternary_kernel_elementary_and_card_dvd_nine
    {E : Type*} [Group E] [Finite E] (f : Cover E S)
    (ho : Odd (Nat.card f.toMonoidHom.ker)) :
    IsElementaryAbelian 3 f.toMonoidHom.ker ∧ Nat.card f.toMonoidHom.ker ∣ 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L⟩ := nonempty_cubicDefectLift f
  obtain ⟨hN,s,hs⟩ := L.exists_quotient_section
  let : L.defect.Normal := hN
  let g := f.quotientKernelSubgroup L.defect L.defect_le_kernel
  have hc : Nat.card f.toMonoidHom.ker=Nat.card L.defect * Nat.card g.toMonoidHom.ker :=
    f.card_kernel_quotientKernelSubgroup L.defect L.defect_le_kernel
  have ho' : Odd (Nat.card g.toMonoidHom.ker) := Odd.of_dvd_nat ho (by
    rw [hc]
    exact dvd_mul_left _ _)
  have h3 := kernel_isPGroup_of_odd (form 4) Nat.prime_three (by decide)
    FiniteField.Nine.natCard (form_conj_cube 4) g ho'
  have hn : ¬ 3 ∣ Nat.card g.toMonoidHom.ker :=
    not_dvd_card_kernel_of_section g positive positive_not_three_dvd_index s hs
  have hg1 : Nat.card g.toMonoidHom.ker=1 := by
    obtain ⟨k,hk⟩ := h3.exists_card_eq
    rw [hk]
    by_cases h0 : k=0
    · rw [h0,pow_zero]
    · exact (hn (hk ▸ dvd_pow_self 3 h0)).elim
  rw [hg1,mul_one] at hc
  have heq : L.defect=f.toMonoidHom.ker :=
    Subgroup.eq_of_le_of_card_ge L.defect_le_kernel hc.le
  have hz : IsElementaryAbelian 3 (zpowers L.z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one L.z_cube
  have hw : IsElementaryAbelian 3 (zpowers L.w) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one L.w_cube
  let := hz
  let := hw
  have hD : IsElementaryAbelian 3 L.defect :=
    IsElementaryAbelian.sup_of_le_centralizer (by
      apply (zpowers_le.mpr (f.ker_le_center L.w_mem)).trans
      exact center_le_centralizer _)
  refine ⟨?_,?_⟩
  · rw [← heq]
    exact hD
  · rw [← heq]
    exact L.defect_card_dvd_nine

public theorem center_elementary_three_and_card_dvd_nine
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hcard : Nat.card F=9) (hconj : ∀ x, J.conj x=x^3)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center E))) :
    IsElementaryAbelian 3 (center E) ∧ Nat.card (center E) ∣ 9 := by
  obtain ⟨eM⟩ := exists_model_equiv J hcard hconj
  let c := centralQuotientCover (e.trans eM)
  have hh := ternary_kernel_elementary_and_card_dvd_nine c
    (by simpa only [c,centralQuotientCover_ker] using ho)
  change IsElementaryAbelian 3 c.toMonoidHom.ker ∧ Nat.card c.toMonoidHom.ker ∣ 9 at hh
  rwa [show c.toMonoidHom.ker=center E from centralQuotientCover_ker (e.trans eM)] at hh

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
