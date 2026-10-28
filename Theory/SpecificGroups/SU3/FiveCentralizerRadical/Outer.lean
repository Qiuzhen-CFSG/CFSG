module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Cyclic two-groups in the outer automorphism group of odd-prime PSU₃

The diagonal outer image has exponent three. Thus a two-group intersects it
trivially and embeds in the cyclic field quotient. Standard-form transport
retains the original Hermitian involution and the actual projective group.
No bound on elementary rank is used to infer cyclicity.

Source: GLS3, Theorem 2.5.12 and §2.7; the application is the PSU₃(5)
centralizer argument in Aschbacher--Smith E.1.14(7), printed p.214.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.FiveCentralizerRadical
variable {E P : Type*} [Field E] [Finite E] [Group P]

/-- Every faithfully represented outer two-group is cyclic under full
unitary-semilinear coverage. -/
theorem isCyclic_of_outer_injective_of_coverage (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (hP : IsPGroup 2 P)
    (f : P →* MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) : IsCyclic P := by
  let N := J.unitaryOuterHom.range
  let : N.Normal := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let : IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) ⧸ N) :=
    J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let g := (QuotientGroup.mk' N).comp f
  apply isCyclic_of_injective g
  apply (MonoidHom.ker_eq_bot_iff g).mp
  apply bot_unique
  intro x hx
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff (N := N) (f x)).mp hx
  have hc : (f x) ^ 3 = 1 := by
    rw [← hu]
    obtain ⟨b, hb⟩ := J.unitaryConj_cube_is_inner u
    change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (J.unitaryConjHom u)) ^ 3 = 1
    rw [← map_pow, J.unitaryConjHom_apply, hb]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
  have hx3 : x ^ 3 = 1 := hf (by simpa only [map_pow, map_one] using hc)
  apply mem_bot.mpr
  apply orderOf_eq_one_iff.mp
  exact Nat.dvd_one.mp ((hP.orderOf_coprime (by decide : Nat.Coprime 2 3) x).gcd_eq_one ▸
    Nat.dvd_gcd (dvd_refl _) (orderOf_dvd_of_pow_eq_one hx3))

open OddPrimeSylow.NormalizedOuter.FormTransport

/-- The cyclicity result for any Hermitian form over the prime-square field.
Simplicity is inherited from the source group. -/
theorem isCyclic_of_outer_injective (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hP : IsPGroup 2 P)
    (f : P →* MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) : IsCyclic P := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J p hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    e.symm.isSimpleGroup
  exact isCyclic_of_outer_injective_of_coverage (standardForm J) rfl
    (OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
      (standardForm J) rfl hp ho hcard hfixed) hP
    ((MulAut.outerCongr e).toMonoidHom.comp f) ((MulAut.outerCongr e).injective.comp hf)

end BenderSuzuki.MatrixGroups.HermitianForm.FiveCentralizerRadical
