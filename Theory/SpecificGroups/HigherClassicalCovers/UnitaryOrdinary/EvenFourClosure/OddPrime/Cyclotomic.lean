module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.QuarticLinear
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence

/-!
# Cyclic odd Sylow subgroups outside the quadratic unitary factors

For q = 2^n, the actual exterior-square action of SU₄(q) descends to
six dimensions over GF(q). Its scalar-sign kernel is trivial on odd
subgroups, so primes dividing q²+1 have cyclic Sylow subgroups by the
quartic torus in GL₆(q). The natural four-dimensional action over GF(q²)
handles all primes outside q⁴−1. Together these exclude every odd prime
outside q²−1 from each finite perfect central covering kernel.

The argument extends the prime-parameter calculation in
`Nondefining.UnitaryCyclotomic.QuarticExterior` to binary extension fields.
All field and form equivalences are actual matrix-group equivalences.
This is the cyclic-Sylow part of Aschbacher–Smith I.1.2–4, printed
pp.407–408 of `refs/quasithin.pdf`, and GLS3 §6.1.
-/

open Matrix BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
open ClassicalOrthogonal.Minus ClassicalOrthogonal.Minus.OddSixComparison
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic

public noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime

private theorem model_subgroup_isCyclic (n : ℕ) [NeZero n]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ (2 ^ n) ^ 2 + 1)
    (P : Subgroup (unitaryForm 2 n).specialSubgroup) (hP : IsPGroup p P) : IsCyclic P := by
  let K := GaloisField 2 n
  have hcard : Nat.card K = 2 ^ n := GaloisField.card 2 n (NeZero.ne n)
  let a := Geometry.orthogonalAction 2 n K hcard
  let f : P →* FullOrthogonal K := a.comp P.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro g hg
    change g = 1
    have hfg : a g.val = 1 := MonoidHom.mem_ker.mp hg
    have hs := (Geometry.orthogonalAction_eq_one_iff_sign 2 n K hcard g.val).mp hfg
    have hsq : g ^ 2 = 1 := by
      rw [pow_two]
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change g.val.val.val * g.val.val.val = 1
      rcases hs with h | h <;> rw [h] <;> simp
    by_contra hn
    have hdiv : p ∣ 2 := (hP.dvd_orderOf hn).trans (orderOf_dvd_of_pow_eq_one hsq)
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdiv)
  let b := Module.finBasisOfFinrankEq K (Space K 2)
    (show Module.finrank K (Space K 2) = 6 by rw [space_finrank])
  let e := Matrix.GeneralLinearGroup.toLin' b
  let c := LinearMap.GeneralLinearGroup.generalLinearEquiv K (Space K 2)
  let μ : P →* GL (Fin 6) K :=
    e.symm.toMonoidHom.comp (c.symm.toMonoidHom.comp
      ((FullOrthogonal K).subtype.comp f))
  have hμ : Function.Injective μ := e.symm.injective.comp
    (c.symm.injective.comp ((FullOrthogonal K).subtype_injective.comp hf))
  apply isCyclic_of_injective_gl_six hp ?_ ?_ hP μ hμ
  · rw [hcard]
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  · rwa [hcard]

variable {F : Type*} [Field F] [Finite F]

theorem special_sylow_isCyclic_of_dvd_sq_add_one
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ (2 ^ n) ^ 2 + 1)
    (P : Sylow p J.specialSubgroup) : IsCyclic P := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨e⟩ := J.nonempty_specialEquiv_of_card (unitaryForm 2 n) (2 ^ n) hcard
    (UnitaryFourFormTransport.fixed_card J n hn hcard hconj) (card_extension 2 n)
    (UnitaryFourFormTransport.fixed_card (unitaryForm 2 n) n hn (card_extension 2 n)
      (unitaryForm_conj 2 n))
  have hc := model_subgroup_isCyclic n hp hd
    ((P : Subgroup J.specialSubgroup).map e.toMonoidHom) (P.isPGroup'.map e.toMonoidHom)
  exact ((P : Subgroup J.specialSubgroup).equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr hc

theorem special_sylow_isCyclic_of_not_dvd_sq_sub_one
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (P : Sylow p J.specialSubgroup) : IsCyclic P := by
  by_cases hplus : p ∣ (2 ^ n) ^ 2 + 1
  · exact special_sylow_isCyclic_of_dvd_sq_add_one J n hn hcard hconj hp hplus P
  have hfour : ¬ p ∣ (2 ^ n) ^ 4 - 1 := by
    have he : (2 ^ n) ^ 4 - 1 = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 + 1) := by
      calc
        _ = ((2 ^ n) ^ 2) ^ 2 - 1 ^ 2 := by ring_nf
        _ = _ := by rw [Nat.sq_sub_sq]; ac_rfl
    rw [he]
    exact (Fact.out : p.Prime).not_dvd_mul hd hplus
  apply subgroup_isCyclic_of_not_dvd_sq_sub_one hp ?_ ?_ J.specialSubgroup
    (P : Subgroup J.specialSubgroup) P.isPGroup'
  · rw [hcard]
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow ((Fact.out : p.Prime).dvd_of_dvd_pow h)))
  · simpa only [hcard, ← pow_mul, Nat.mul_assoc] using hfour

theorem not_dvd_kernel_of_not_dvd_sq_sub_one
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  exact d.not_dvd_card_multiplier_of_isCyclic_sylow
    (special_sylow_isCyclic_of_not_dvd_sq_sub_one
      (UnitaryFourFormTransport.standardForm J) n hn hcard hconj hp hd)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
