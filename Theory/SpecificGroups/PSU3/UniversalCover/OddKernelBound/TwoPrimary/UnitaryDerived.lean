module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.UnitaryDerived.CyclicQuotient
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.UnitaryDerived.Linear
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.MatrixGroups.SpecialUnitaryFixedEquiv
public import BenderSuzuki.External.Huppert.II.theorem_10_4

/-!
# Derived kernels of central two-extensions of GU₂

For an identity-Gram Hermitian form over a finite field of order q², with
stored involution x ↦ x^q and q any odd prime power, every finite central
two-extension of its actual unitary group has trivial derived kernel.
Neither the unitary group nor the extension is assumed perfect.

The literal determinant has cyclic image in the field's multiplicative
group. Its kernel is the original special unitary subgroup. A norm-minus-one
element and a nonzero anti-fixed element give the basis change identifying
that subgroup with SL₂ over the actual fixed subfield. The existing
cyclic/quaternion Sylow theorem proves local derived-kernel vanishing there;
`Linear` supplies its odd abelianization, including at q = 3. The normal
subgroup construction of `CyclicQuotient` then proves the full GU₂ result.

This discharges the local-calculation input to the published
`not_two_dvd_kernel_of_unitary_local`; the actual projective local geometry
remains with its independent owner. Source: the two-primary calculation
supporting GLS3 §6.1 and Aschbacher--Smith I.1.3(2), I.1.4(2), printed
pp.407--408 (PDF pp.418--419). The SU₂ coordinate comparison is the matrix
argument of ABG II.2 Lemma 1(vi), article p.17.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
universe u
private theorem exists_special_equiv_fixed_odd {F : Type u} [Field F] [Finite F]
    (J : HermitianForm 2 F) (hJ : J.form = 1)
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    (2 : FixedBy.subfield F J.conj) ≠ 0 ∧
      Nonempty (J.specialSubgroup ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := e * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have h2 : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hodd
  have h2K : (2 : FixedBy.subfield F J.conj) ≠ 0 := by
    intro h
    exact h2 (congrArg Subtype.val h)
  have hk : Nat.card {x : F // J.conj x = x} = p ^ e :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj p e he hcard hconj
  obtain ⟨z, _, hz⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    J (p ^ e) hcard hk (-1) (by simp) (by simp)
  have hex : ∃ a : F, J.conj a ≠ a := by
    by_contra! hall
    let eqv : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun a => ⟨a, hall a⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := Nat.card_congr eqv
    rw [hk, hcard] at hh
    have hq : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
    nlinarith
  obtain ⟨a, ha⟩ := hex
  let t := a - J.conj a
  have ht0 : t ≠ 0 := sub_ne_zero.mpr ha.symm
  have ht : J.conj t = -t := by
    dsimp [t]
    rw [map_sub, J.conj_involutive a]
    ring
  obtain ⟨C, _, hC⟩ := J.exists_skew_basis hJ h2 z t hz ht0 ht
  exact ⟨h2K, ⟨J.specialUnitaryEquivFixed C (2 * t) (mul_ne_zero h2 ht0) hC⟩⟩

private noncomputable def determinantKernelEquivSpecial {F : Type u} [Field F]
    (J : HermitianForm 2 F) :
    (GeneralLinearGroup.det.comp J.unitarySubgroup.subtype).ker ≃* J.specialSubgroup where
  toFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
end BenderSuzuki.MatrixGroups.HermitianForm
open PerfectCentralCovering
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
universe u v
/-- Every finite central two-extension of the actual GU₂ has kernel disjoint
from its derived subgroup. The extension universe is arbitrary, and all odd
prime powers are included, in particular q = 3, 5, 9, and 25. -/
public theorem unitary_twoKernelDerivedTrivial
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 2 F) (hJ : J.form = 1)
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    TwoKernelDerivedTrivial.{v, u} J.unitarySubgroup := by
  obtain ⟨h2, ⟨e0⟩⟩ := J.exists_special_equiv_fixed_odd hJ hp hodd he hcard hconj
  let d := GeneralLinearGroup.det.comp J.unitarySubgroup.subtype
  let a := (J.determinantKernelEquivSpecial).trans e0
  apply PerfectCentralCovering.twoKernelDerivedTrivial_of_cyclic_quotient d
  · rw [Nat.card_congr a.abelianizationCongr.toEquiv]
    exact Matrix.SpecialLinearGroup.odd_card_abelianization h2
  · intro D _ _ f hf hc hk
    let g := a.toMonoidHom.comp f
    have hgker : g.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ a.injective
    have h := CentralExtension.ker_inf_commutator_eq_bot_of_cyclic_or_quaternion_sylow
      g (a.surjective.comp hf) (by rw [hgker]; exact hc)
      (by rw [hgker]; exact hk)
      (Matrix.SpecialLinearGroup.sylow_two_cyclic_or_quaternion h2)
    simpa only [hgker] using h
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
