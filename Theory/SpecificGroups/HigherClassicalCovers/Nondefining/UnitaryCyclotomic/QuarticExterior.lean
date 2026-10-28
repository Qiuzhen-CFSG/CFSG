module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.QuarticLinear
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization

/-!
# The quartic unitary Sylow calculation via the exterior square

The signed exterior-square construction descends the genuine SU₄ action
to a six-dimensional quadratic space over the fixed field. Its kernel is
exactly the scalar signs. Thus an odd Sylow subgroup acts faithfully in
GL₆(p); the quartic field torus proves its cyclicity for r ∣ p²+1.
Finite-field and orthonormal-basis transport retain arbitrary coefficient
fields and arbitrary nondegenerate Hermitian forms with p-Frobenius.

Only the constructed action and its kernel are used; no orthogonal image
or exceptional-isomorphism theorem is needed. This supplies the quartic
case of the covering-kernel input in Aschbacher–Smith A.2.17, printed p.39,
including r=5 for PSU₄(3). The exterior construction is GLS3 §2.7.
-/

open Matrix BenderSuzuki.MatrixGroups
open ClassicalOrthogonal.Minus ClassicalOrthogonal.Minus.OddSixComparison
noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic

private theorem model_subgroup_isCyclic {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p ^ 2 + 1)
    (P : Subgroup (unitaryForm p 1).specialSubgroup) (hP : IsPGroup r P) : IsCyclic P := by
  let hcard : Nat.card (ZMod p) = p ^ 1 := by simp
  let a := Geometry.orthogonalAction p 1 (ZMod p) hcard
  let f : P →* FullOrthogonal (ZMod p) := a.comp P.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro g hg
    change g = 1
    have hfg : a g.val = 1 := MonoidHom.mem_ker.mp hg
    have hs := (Geometry.orthogonalAction_eq_one_iff_sign p 1 (ZMod p) hcard g.val).mp hfg
    have hsq : g ^ 2 = 1 := by
      rw [pow_two]
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change g.val.val.val * g.val.val.val = 1
      rcases hs with h | h <;> rw [h] <;> simp
    by_contra hn
    have hrdiv : r ∣ 2 := (hP.dvd_orderOf hn).trans (orderOf_dvd_of_pow_eq_one hsq)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp hrdiv)
  let b := Module.finBasisOfFinrankEq (ZMod p) (Space (ZMod p) 2)
    (show Module.finrank (ZMod p) (Space (ZMod p) 2) = 6 by rw [space_finrank])
  let e := Matrix.GeneralLinearGroup.toLin' b
  let c := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Space (ZMod p) 2)
  let μ : P →* GL (Fin 6) (ZMod p) :=
    e.symm.toMonoidHom.comp (c.symm.toMonoidHom.comp
      ((FullOrthogonal (ZMod p)).subtype.comp f))
  have hμ : Function.Injective μ := e.symm.injective.comp
    (c.symm.injective.comp ((FullOrthogonal (ZMod p)).subtype_injective.comp hf))
  apply isCyclic_of_injective_gl_six hr2 ?_ ?_ hP μ hμ
  · simpa only [Nat.card_zmod] using
      (fun h => hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime)
        (Fact.out : p.Prime)).mp h) : ¬ r ∣ p)
  · simpa only [Nat.card_zmod] using hd

/-- For every actual Hermitian form over p² with p-Frobenius, the Sylow
subgroups at odd primes dividing p²+1 are cyclic. -/
public theorem special_sylow_isCyclic_of_dvd_sq_add_one
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F)
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p ^ 2 + 1)
    (P : Sylow r J.specialSubgroup) : IsCyclic P := by
  classical
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hmodel : Nat.card (Extension p 1) = p ^ 2 := by
    simpa only [pow_one] using card_extension p 1
  have hmodelconj : ∀ x, (unitaryForm p 1).conj x = x ^ p := by
    intro x
    simpa only [pow_one] using unitaryForm_conj p 1 x
  obtain ⟨e⟩ := J.nonempty_specialEquiv_of_card (unitaryForm p 1) p hF
    (J.card_fixed_of_prime_frobenius hconj) hmodel
    ((unitaryForm p 1).card_fixed_of_prime_frobenius hmodelconj)
  have hc := model_subgroup_isCyclic hr2 hrp hd
    ((P : Subgroup J.specialSubgroup).map e.toMonoidHom) (P.isPGroup'.map e.toMonoidHom)
  exact ((P : Subgroup J.specialSubgroup).equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr hc

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic
