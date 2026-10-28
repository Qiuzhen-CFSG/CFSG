module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Defining-prime divisibility for the unitary group in dimension three

The explicit upper root group has order `p³`. Transporting a nondegenerate
Hermitian form to the standard form embeds that group in the projective
unitary group. The coefficient field has order `p²`; the fixed field has
order `p`. In coefficient-field order nine the scalar kernel of the special
to projective map is trivial: its scalars have both cube and eighth power
one. Thus this map gives an actual equivalence SU₃(3) ≃ PSU₃(3).

These are the order and central-quotient calculations used in
Aschbacher--Smith, G.7.2(3), printed pp.347--348.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The defining-prime cube divides the order of the actual projective group. -/
theorem prime_cube_dvd_card_projective {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    p ^ 3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hcard) (by simpa using hconj)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  rw [Nat.card_congr e.toEquiv]
  have hroot := Coverage.rootGroup_card (FormTransport.standardForm J) rfl p hcard hfixed
  rw [← hroot]
  exact Subgroup.card_subgroup_dvd_card _

/-- Passing to the special group preserves the defining-prime divisibility. -/
theorem prime_cube_dvd_card_special {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    p ^ 3 ∣ Nat.card J.specialSubgroup :=
  (J.prime_cube_dvd_card_projective hp hcard hconj).trans
    (Subgroup.card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)

/-- In coefficient-field order nine the canonical projective map is injective. -/
theorem specialToProjective_injective_of_card_nine
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 9) : Function.Injective J.specialToProjective := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hz : x.val ∈ Subgroup.center (GL (Fin 3) F) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have hu3 : u ^ 3 = 1 := by
    have hd := x.property.2
    change Matrix.GeneralLinearGroup.det x.val = 1 at hd
    rw [← hu, Matrix.GeneralLinearGroup.det_scalar] at hd
    simpa using hd
  have hu8 : orderOf u ∣ 8 := by
    simpa only [Nat.card_units, hcard] using orderOf_dvd_natCard u
  have hu1 : u = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 8)
      (orderOf_dvd_of_pow_eq_one hu3) hu8)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

/-- The genuine special/projective comparison at fixed-field order three. -/
noncomputable def specialProjectiveEquivOfCardNine
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 9) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective J.specialToProjective
    ⟨J.specialToProjective_injective_of_card_nine hcard, J.specialToProjective_surjective⟩

end BenderSuzuki.MatrixGroups.HermitianForm
