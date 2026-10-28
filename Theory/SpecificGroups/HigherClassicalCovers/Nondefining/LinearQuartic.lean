module

public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.GroupTheory.PerfectCentralCover
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Quartic primes in degree-four linear covering kernels

For an odd prime r dividing p²+1, the residue of p modulo r has order four.
The faithful natural action of a Sylow r-subgroup of SL₄(F), where |F|=p,
has the least possible nondefining degree. A central subgroup of order r
acts irreducibly, and its endomorphism field makes the whole Sylow subgroup
cyclic. Surjective Sylow transport retains cyclicity in the literal PSL₄
quotient. Central transfer then excludes r from every finite perfect central
covering kernel. This works also for p=3 and for arbitrary coefficient fields.

This proves the quartic branch of the nondefining-kernel input to
Aschbacher–Smith A.2.17, printed p.39. Coverings and cyclic-Sylow transfer
follow I.1.1–I.1.2, printed p.407. The linear representation argument is the
Singer-centralizer theorem formalized in `CyclotomicPrimeCyclicity`.
-/

open Matrix PerfectCentralCovering
open scoped MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

private theorem orderOf_eq_four {p r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hd : r ∣ p^2 + 1) : orderOf (p : ZMod r) = 4 := by
  have hs : (p : ZMod r)^2 = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (p^2+1) r).mpr hd
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hn : (p : ZMod r)^2 ≠ 1 := by
    rw [hs]
    intro h
    have ht : (2 : ZMod r) = 0 := by linear_combination -h
    have hdiv := (ZMod.natCast_eq_zero_iff 2 r).mp ht
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp hdiv)
  have hpw : (p : ZMod r)^4 = 1 := by
    calc
      (p : ZMod r)^4 = ((p : ZMod r)^2)^2 := by ring
      _ = 1 := by rw [hs]; ring
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hn) (by simpa using hpw)

private theorem sl_cyclic {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hrp : r ≠ p) (hord : 4 ≤ orderOf (p : ZMod r))
    (P : Sylow r SL(4,F)) : IsCyclic P := by
  classical
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by rwa [← Nat.card_eq_fintype_card])
  let ρ : Representation F P (Fin 4 → F) :=
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp SpecialLinearGroup.coeMonoidHom).comp
      (P : Subgroup SL(4,F)).subtype
  have hi : Function.Injective ρ :=
    Matrix.toLinAlgEquiv'.injective.comp
      (SpecialLinearGroup.coeMonoidHom_injective.comp (P : Subgroup SL(4,F)).subtype_injective)
  refine Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree P.isPGroup'
    (CharP.cast_ne_zero_of_ne_of_prime F (Fact.out : r.Prime) hrp.symm) ?_ ρ hi ?_
  · rw [← Nat.card_eq_fintype_card, hF]
    intro hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (Fact.out : p.Prime)).mp hd)
  · simpa only [Module.finrank_fin_fun, ← Nat.card_eq_fintype_card, hF] using hord

/-- Quartic primes have cyclic Sylow subgroups in the literal projective quotient. -/
public theorem linear_sylow_isCyclic_of_dvd_sq_add_one
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^2 + 1)
    (P : Sylow r PSL(4,F)) : IsCyclic P := by
  let q : SL(4,F) →* PSL(4,F) := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hq r P
  let := sl_cyclic hF hrp (by rw [orderOf_eq_four hr2 hd]) Q
  have hc : IsCyclic ((Q : Subgroup SL(4,F)).map q) :=
    isCyclic_of_surjective _ (q.subgroupMap_surjective (Q : Subgroup SL(4,F)))
  rwa [← Sylow.coe_mapSurjective hq, hQ] at hc

/-- The quartic-prime exclusion for every actual finite perfect central cover. -/
public theorem linear_not_dvd_kernel_of_dvd_sq_add_one
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^2 + 1)
    {E : Type*} [Group E] [Finite E] (f : Cover E PSL(4,F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (linear_sylow_isCyclic_of_dvd_sq_add_one hF hr2 hrp hd)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
