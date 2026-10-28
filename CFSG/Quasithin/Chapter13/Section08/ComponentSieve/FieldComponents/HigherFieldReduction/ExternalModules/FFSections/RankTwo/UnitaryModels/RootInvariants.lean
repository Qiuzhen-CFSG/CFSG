module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Residual
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Root invariants for the even-degree unitary model comparison

The Hermitian root subgroup has order 2^(3*n) and odd index in PSU₃(2^n).
Its square formula forces every element of order at most two into the
vertical coordinate subgroup. That subgroup injects into the fixed field,
of order 2^n, so the two-rank is at most n. An actual Hermitian basis change
transports both invariants to the original projective matrix carrier.

The Sylow-index argument follows `Theory.SpecificGroups.SU3.EvenTwoRank`.
Here the already constructed `EvenInner.rootImage` keeps the calculation
independent of graph-automorphism comparison modules, so it can be used
with the Chapter 13 graph-fixed interfaces. Only the upper rank bound
consumed by the model exclusion is asserted.

Source: Huppert II.10.12 and Aschbacher–Smith, the unitary comparison in
the proof of 13.8.20, printed p.954; see also the rank table, printed p.356.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels

variable {E : Type*} [Field E]

private def vertical (J : HermitianForm 3 E) : Subgroup (hermitianUnipotentCoord J) where
  carrier := {z | z.val.1 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change x.val.1 + y.val.1 = 0
    rw [hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    change -x.val.1 = 0
    rw [hx, neg_zero]

private theorem coord_rank_le [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    primeRank 2 (hermitianUnipotentCoord J) ≤ n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : vertical J → {x : E // J.conj x = x} := fun z => ⟨z.val.val.2, by
    have hz := z.val.property
    have hz0 : z.val.val.1 = 0 := z.property
    rw [hz0, zero_mul, add_zero] at hz
    exact (eq_neg_of_add_eq_zero_right hz).trans (CharTwo.neg_eq _)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (x.property.trans y.property.symm) (congrArg Subtype.val h)
  apply primeRank_le_of_pow_eq_one_subset (vertical J)
    ((Nat.card_le_card_of_injective f hf).trans hfixed.le)
  intro x hx
  have hs := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) hx
  rw [EvenInner.square_coordinates] at hs
  change x.val.1 * J.conj x.val.1 = 0 at hs
  exact (mul_eq_zero.mp hs).elim id ((map_eq_zero J.conj).mp)

variable [Finite E]

private theorem root_index_odd (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    ¬ 2 ∣ (EvenInner.rootImage J hJ).index := by
  let q := 2 ^ n
  have hq : 0 < q := by positivity
  have hqe : 2 ∣ q := dvd_pow_self 2 (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  have hgcd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    have hf : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hf]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _
  have hdiv : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hi := (EvenInner.rootImage J hJ).card_mul_index
  rw [EvenInner.rootImage_card J hJ hcard hfixed] at hi
  have hprod : (EvenInner.rootImage J hJ).index * Nat.gcd 3 (q + 1) =
      (q ^ 3 + 1) * (q ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 3)
    calc
      q ^ 3 * ((EvenInner.rootImage J hJ).index * Nat.gcd 3 (q + 1)) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd 3 (q + 1) := by
            rw [← mul_assoc, hi]
      _ = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
        rw [hGcard, Nat.div_mul_cancel hdiv]
      _ = q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by ring
  intro hbad
  have hd : 2 ∣ (q ^ 3 + 1) * (q ^ 2 - 1) :=
    hprod ▸ dvd_mul_of_dvd_left hbad _
  rcases Nat.prime_two.dvd_mul.mp hd with h | h
  · exact Nat.prime_two.not_dvd_one
      ((Nat.dvd_add_iff_right (hqe.trans (dvd_pow_self q (by decide : 3 ≠ 0)))).mpr h)
  · have hsq : 1 ≤ q ^ 2 := one_le_pow₀ (by omega)
    have hp2 : 2 ∣ q ^ 2 := hqe.trans (dvd_pow_self q (by decide : 2 ≠ 0))
    rw [← Nat.sub_add_cancel hsq] at hp2
    exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hp2)

private theorem standard_invariants (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ n ∧
      (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization 2 = 3 * n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (EvenInner.rootImage_isTwoGroup J hJ hcard hfixed).toSylow
      (root_index_odd J hJ hn hcard hfixed)
  constructor
  · rw [S.primeRank_eq]
    change primeRank 2 (hermitianUnipotentPSU J hJ).range ≤ n
    rw [← primeRank_equiv 2 (MonoidHom.ofInjective (EvenInner.root_injective J hJ))]
    exact coord_rank_le J hfixed
  · have hs := S.card_eq_multiplicity
    have hr : Nat.card S = 2 ^ (3 * n) := by
      change Nat.card (EvenInner.rootImage J hJ) = _
      rw [EvenInner.rootImage_card J hJ hcard hfixed, ← pow_mul, Nat.mul_comm n 3]
    rw [hr] at hs
    exact (Nat.pow_right_injective (by decide : 1 < 2) hs).symm

/-- The root Sylow supplies precisely the rank upper bound and two-part
needed to distinguish the projective unitary carrier from the B.4.2 models. -/
public theorem projective_invariants (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ n ∧
      (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization 2 = 3 * n := by
  have hf : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hf
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  rw [primeRank_equiv 2 e, Nat.card_congr e.toEquiv]
  exact standard_invariants (standardForm J) rfl hn hcard hf

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels
