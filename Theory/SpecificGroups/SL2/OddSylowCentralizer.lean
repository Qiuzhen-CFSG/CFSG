module
public import Theory.SpecificGroups.SL2.SylowBorelSeparation
/-!
# Odd centralizers in a characteristic-two Sylow subgroup

A nonidentity element of odd order in SL₂(F) centralizes no nonidentity
Sylow two element. Conjugate the Sylow subgroup to the upper root group.
Its nontrivial centralizer lies in the Borel, where the commutation equation
forces the diagonal entries to be one. The odd element would then have
order dividing two, a contradiction.

This is the quotient calculation used for the natural-block fixed subgroup
in Aschbacher–Smith, Lemma 2.4.8(5), printed p.530.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem eq_one_of_sylow_commutes_nontrivial_odd (P : Sylow 2 SL(2,F))
    (r d : SL(2,F)) (hr : r ∈ P) (hd : d ≠ 1)
    {m : ℕ} (hm : Odd m) (hdm : d^m = 1) (hc : Commute r d) : r = 1 := by
  by_contra hr1
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) P (upperUnipotentSylow F 2)
  let c := MulAut.conj a
  have hP : (P : Subgroup SL(2,F)).map c.toMonoidHom = upperUnipotent F := by
    change ((a • P : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hru : c r ∈ upperUnipotent F := hP ▸ mem_map_of_mem c.toMonoidHom hr
  have hcr : c r ≠ 1 := fun he => hr1 (c.map_eq_one_iff.mp he)
  have hcd : c d ≠ 1 := fun he => hd (c.map_eq_one_iff.mp he)
  have hcomm : c d * c r * (c d)⁻¹ = c r := by
    rw [←map_mul,←map_inv,←map_mul]
    have he : d*r*d⁻¹=r := by rw [hc.symm.eq,mul_assoc,mul_inv_cancel,mul_one]
    rw [he]
  have hdb : c d ∈ rankOneBorel F := mem_borel_of_conjugate_unipotent_mem_borel
    (c r) (c d) hru hcr (by rw [hcomm]; exact (upperUnipotent F).le_normalizer hru)
  obtain ⟨t,ht⟩ := (mem_upperUnipotent F _).mp hru
  have ht0 : t ≠ 0 := by
    intro he
    rw [he,transvection_coeff_zero] at ht
    exact hcr ht.symm
  have hsquare : (c d).val 0 0 ^ 2 = 1 := by
    have he := hcomm
    rw [←ht,triangular_conj_upper ((mem_rankOneBorel_iff _).mp hdb)] at he
    have hcoeff := congrArg (fun g : SL(2,F) => g.val 0 1) he
    simp only [transvection_coe] at hcoeff
    exact mul_right_cancel₀ ht0 (by simpa using hcoeff)
  have h00 : (c d).val 0 0 = 1 := by
    apply (frobenius_inj F 2)
    simpa [frobenius_def] using hsquare
  have h10 := (mem_rankOneBorel_iff _).mp hdb
  have h11 : (c d).val 1 1 = 1 := by
    simpa only [det_fin_two,h00,h10,one_mul,mul_zero,sub_zero] using (c d).property
  have hdu : c d ∈ upperUnipotent F := by
    refine (mem_upperUnipotent F _).mpr ⟨(c d).val 0 1,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe,h00,h10,h11]
  obtain ⟨b,hb⟩ := (mem_upperUnipotent F _).mp hdu
  have hd2 : (c d)^2 = 1 := by
    rw [←hb,pow_two,←transvection_add,CharTwo.add_self_eq_zero,transvection_coeff_zero]
  have hod : orderOf (c d) = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.coprime_two_left.mpr hm) (orderOf_dvd_of_pow_eq_one hd2)
    (orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hdm,map_one]))
  exact hcd (orderOf_eq_one_iff.mp hod)

end Matrix.SpecialLinearGroup

