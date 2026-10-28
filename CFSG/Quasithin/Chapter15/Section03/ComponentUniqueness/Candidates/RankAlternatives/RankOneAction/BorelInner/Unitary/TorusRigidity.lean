module

public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Mathlib.FieldTheory.Fixed

/-!
# Innerness detected by the norm-one torus

The proved semilinear coverage theorem represents an arbitrary automorphism
of the simple binary PSU₃ model by a unitary matrix and a field automorphism.
Preserving the root forces the unitary matrix to be triangular. Its action
on the full torus modulo the root is then exactly the field automorphism.

For even n the projective torus parametrization is injective, since its
scalar kernel has order dividing both 3 and 2^n+1. Fixation of the norm-one
torus forces fixation of 2^n+1 field elements. A proper subfield has at most
2^n elements, so the field part is trivial. The same coprimality kills the
diagonal outer image. No restriction to involutory actors is used.

Source: Aschbacher--Smith 15.3.37, printed p.1135; Huppert II.10.12
for the root and torus matrices; GLS3, Theorem 2.5.12 and §2.7 for
semilinear automorphisms, proved in `EvenSemilinear`.
-/

public section

open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem coprime_three_normOrder {n : ℕ} (heven : Even n) :
    Nat.Coprime 3 (2 ^ n + 1) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hm := Nat.BinaryTorusParity.two_pow_mod_three n
  rw [Nat.even_iff.mp heven, if_pos rfl] at hm
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem field_eq_one_of_normOne_fixed {q : ℕ}
    (hcard : Nat.card E = q ^ 2) (hconj : ∀ x : E, J.conj x = x ^ q)
    (σ : E ≃+* E) (hfix : ∀ k : EvenInner.normOne J, σ (k.val : E) = k.val) :
    σ = 1 := by
  by_contra hne
  let : Finite (E ≃+* E) := Finite.of_injective
    (fun a : E ≃+* E => (a : E → E)) DFunLike.coe_injective
  let H := Subgroup.zpowers σ
  let K := FixedPoints.subfield H E
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank K E = orderOf σ := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers]
  have ho : 2 ≤ orderOf σ := by
    have hp := orderOf_pos σ
    have hh : orderOf σ ≠ 1 := fun he => hne (orderOf_eq_one_iff.mp he)
    omega
  have hs : Nat.card K ^ 2 ≤ Nat.card E := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hd]
    have hk : 0 < Nat.card K := Nat.card_pos
    exact Nat.pow_le_pow_right (by omega) ho
  let f : EvenInner.normOne J → K := fun k => ⟨k.val, fun g =>
    smul_eq_self_of_mem_zpowers g.property (hfix k)⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Units.ext (congrArg Subtype.val hab))
  have hl := Nat.card_le_card_of_injective f hf
  rw [EvenInner.normOne_card J hcard hconj] at hl
  rw [hcard] at hs
  nlinarith


omit [Finite E] in
private theorem projective_torus_injective_of_even
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (heven : Even n)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    Function.Injective (hermitianTorusPSU J hJ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro k hk
  obtain ⟨hnorm, hcube⟩ := (BorelTorus.projective_eq_one_iff J hJ k).mp hk
  have hpow : k ^ (2 ^ n + 1) = 1 := by
    rw [EvenInner.normOne_eq_rootsOfUnity J hconj] at hnorm
    simpa only [mem_rootsOfUnity] using hnorm
  exact (pow_eq_one_iff_of_coprime (coprime_three_normOrder heven)).mp ⟨hcube, hpow⟩

theorem inner_of_normOne_displacement
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hroot : (BorelTorus.projectiveRoot J hJ).map a.toMonoidHom =
      BorelTorus.projectiveRoot J hJ)
    (hfix : ∀ k : EvenInner.normOne J,
      a (hermitianTorusPSU J hJ k.val) * (hermitianTorusPSU J hJ k.val)⁻¹ ∈
        BorelTorus.projectiveRoot J hJ) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨σ, hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  obtain ⟨u, hu⟩ := hσ
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨h10, h20, h21⟩ := BorelTorus.SemilinearActors.projective_semilinear_upper
    J hJ hcard hfixed a σ u hu hroot
  have hs : σ = 1 := by
    apply field_eq_one_of_normOne_fixed J hcard hconj σ
    intro k
    have hh := (BorelTorus.SemilinearActors.projective_semilinear_torus_displacement_iff
      J hJ a σ u h10 h20 h21 hu k.val).mp (hfix k)
    exact congrArg Units.val ((projective_torus_injective_of_even J hJ heven hconj) hh)
  have hf : J.HasUnitarySemilinearForm a 1 := hs ▸ ⟨u, hu⟩
  obtain ⟨v, rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hf
  apply (QuotientGroup.eq_one_iff _).mp
  have hv : J.unitaryOuterHom v = 1 := mem_bot.mp
    ((J.unitaryOuterHom_range_eq_bot_of_coprime hconj
      (coprime_three_normOrder heven)) ▸ (show J.unitaryOuterHom v ∈
        J.unitaryOuterHom.range from ⟨v, rfl⟩))
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom v) = 1 at hv
  rw [J.unitaryConjHom_apply] at hv
  exact hv

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary
