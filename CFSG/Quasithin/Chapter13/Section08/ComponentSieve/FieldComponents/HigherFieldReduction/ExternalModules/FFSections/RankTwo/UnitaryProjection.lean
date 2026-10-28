module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import BenderSuzuki.MatrixGroups.RankThreeScalarCongruence

/-!
# The even-degree unitary projection in the external cubic branch

A scalar in the special-to-projective kernel has cube one. A nonidentity
such scalar would have order three, so the Hermitian norm equation would
force the fixed-field order to be two modulo three. An even binary degree
instead gives one modulo three. Thus the literal projection is an
isomorphism. No order formula or simplicity premise is needed.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The coefficient
field has order 2^(2*n); its conjugation is the 2^n power map. This comparison
does not yet exclude the unitary family from the full B.4.2 action list.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

open BenderSuzuki.MatrixGroups Subgroup
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The actual projective projection has trivial kernel at even fixed-field degree. -/
theorem specialToProjective_injective_even {n : ℕ} (hn : Even n)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Function.Injective J.specialToProjective := by
  apply J.specialToProjective.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  have hz : x.val ∈ center (GL (Fin 3) E) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨a, ha⟩ := hz
  have ha3 : a ^ 3 = 1 := by
    have hd := x.property.2
    change Matrix.GeneralLinearGroup.det x.val = 1 at hd
    rw [← ha, Matrix.GeneralLinearGroup.det_scalar] at hd
    simpa using hd
  have ha1 : a = 1 := by
    by_contra hne
    have ho : orderOf a = 3 := orderOf_eq_prime ha3 hne
    have hm := J.mod_three_of_scalar_order_three hconj a ho x
      (congrArg (fun g : GL (Fin 3) E => g.val) ha.symm)
    obtain ⟨m, rfl⟩ := hn
    have hmod : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul]
      norm_num [Nat.pow_mod]
    omega
  apply Subtype.ext
  rw [← ha, ha1, map_one]
  rfl


/-- The comparison uses the original special-to-projective map. -/
def specialProjectiveEquivEven {n : ℕ} (hn : Even n)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective J.specialToProjective
    ⟨specialToProjective_injective_even J hn hconj, J.specialToProjective_surjective⟩

/-- No replacement of the projective map is hidden in the comparison. -/
@[simp] theorem specialProjectiveEquivEven_apply {n : ℕ} (hn : Even n)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (g : J.specialSubgroup) :
    specialProjectiveEquivEven J hn hconj g = J.specialToProjective g := rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
