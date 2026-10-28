module
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.FieldFaithfulness
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal

/-!
# Coprime field actors on a binary unitary Borel

Faithfulness of the semilinear field parameter makes its order divide the
order of the actual projective actor. A trivial parameter makes the cube
inner; coprimality and exclusion of three then make the actor trivial.
Preserving the root group forces the unitary factor to be triangular,
giving the literal displacement formula on the full projective torus.

Source: GLS3, Theorem 2.5.12 and Section 2.7; the Borel argument in
Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelCoprimeFieldAction
open BorelTorus BorelTorus.SemilinearActors
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = (2 ^ n) ^ 2)
variable (hconj : ∀ x, J.conj x = x ^ (2 ^ n))

include hJ hn hc hconj in
/-- The field coefficient retains the order of the original automorphism. -/
theorem coefficient_pow {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    {σ : F ≃+* F} (h : J.HasUnitarySemilinearForm a σ) {k : ℕ}
    (hk : a ^ k = 1) : σ ^ k = 1 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hc hconj
  exact J.semilinear_identity_field_eq_one n hn hJ hc hf (σ ^ k)
    (hk ▸ h.pow J hJ k)

omit [Finite F] in
/-- An odd coprime actor of three-prime order cannot be purely inner-diagonal. -/
theorem coefficient_ne_one {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    {σ : F ≃+* F} (h : J.HasUnitarySemilinearForm a σ)
    (ha : a ≠ 1) (hthree : Nat.Coprime (orderOf a) 3)
    (hcop : Nat.Coprime (orderOf a) (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J))) :
    σ ≠ 1 := by
  rintro rfl
  obtain ⟨u,rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp h
  obtain ⟨b,hb⟩ := J.unitaryConj_cube_is_inner u
  have hcube : (J.unitaryConj u) ^ 3 = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_pow_dvd 3)
    rw [hb]
    exact (orderOf_map_dvd MulAut.conj b).trans (orderOf_dvd_natCard b)
  exact ha (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hthree dvd_rfl
    (orderOf_dvd_of_pow_eq_one hcube)))

include hn hc hconj in
/-- Every nontrivial coprime actor preserving the root has a nontrivial
field coefficient and its exact action on the full torus modulo that root. -/
theorem exists_nontrivial_coefficient
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ≠ 1) (hthree : Nat.Coprime (orderOf a) 3)
    (hcop : Nat.Coprime (orderOf a) (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ) :
    ∃ σ : F ≃+* F, σ ≠ 1 ∧ orderOf σ ∣ orderOf a ∧
      ∀ k : Fˣ, a (BenderSuzuki.External.hermitianTorusPSU J hJ k) *
        (BenderSuzuki.External.hermitianTorusPSU J hJ k)⁻¹ ∈ projectiveRoot J hJ ↔
        BenderSuzuki.External.hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) =
          BenderSuzuki.External.hermitianTorusPSU J hJ k := by
  obtain ⟨σ,hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hc hconj a
  refine ⟨σ, coefficient_ne_one J hσ ha hthree hcop,
    orderOf_dvd_of_pow_eq_one (coefficient_pow J hJ hn hc hconj hσ
      (pow_orderOf_eq_one a)), ?_⟩
  obtain ⟨u,hu⟩ := hσ
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hc hconj
  obtain ⟨h10,h20,h21⟩ := projective_semilinear_upper J hJ hc hf a σ u hu hroot
  exact projective_semilinear_torus_displacement_iff J hJ a σ u h10 h20 h21 hu
open BenderSuzuki.External

omit [Finite F] in
/-- The full projective torus normalizes the literal Hermitian root group. -/
theorem torus_normalizes_root : projectiveTorus J hJ ≤
    normalizer (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hc (k : Fˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J)
      (hx : x ∈ projectiveRoot J hJ) :
      hermitianTorusPSU J hJ k * x * (hermitianTorusPSU J hJ k)⁻¹ ∈ projectiveRoot J hJ := by
    obtain ⟨z, rfl⟩ := hx
    rw [EvenInner.projective_torus_action]
    exact ⟨_, rfl⟩
  rintro _ ⟨k, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc k x
  · intro hx
    have hh := hc k⁻¹ _ hx
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

include hn hc hconj in
/-- A fixed field parameter gives the quotient displacement needed to lift
an element of the torus to the original Sylow normalizer. -/
theorem torus_displacement_of_fixed
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    {σ : F ≃+* F} (hσ : J.HasUnitarySemilinearForm a σ)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (k : Fˣ) (hfix : Units.map σ.toMonoidHom k = k) :
    (hermitianTorusPSU J hJ k)⁻¹ * a (hermitianTorusPSU J hJ k) ∈ projectiveRoot J hJ := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hc hconj
  obtain ⟨u,hu⟩ := hσ
  obtain ⟨h10,h20,h21⟩ := projective_semilinear_upper J hJ hc hf a σ u hu hroot
  have hd := projective_semilinear_torus_displacement J hJ a σ u h10 h20 h21 hu k
  rw [hfix] at hd
  have ht := torus_normalizes_root J hJ ⟨k,rfl⟩
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using
    (mem_normalizer_iff.mp ((normalizer _).inv_mem ht) _).mp hd
end BenderSuzuki.MatrixGroups.HermitianForm.BorelCoprimeFieldAction
