module
public import Theory.ElementaryAbelian.Quotient
public import Theory.Quasithin.CoprimeRank
public import Theory.SpecificGroups.PSL3.NonsplitPrimeRank
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveLinearEmbedding
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.LinearSylow

/-!
# Noncubic prime rank in the full ternary unitary groups

For a nondefining odd prime outside q+1, the cyclic unitary torus controls
primes dividing q-1. For the remaining primes, the actual embedding into
PSL₃ over the quadratic coefficient field gives rank at most one. The
literal SU₃-to-PSU₃ scalar kernel has order dividing three, so the same
bound holds in the full special cover away from three.

Source: Huppert II.10.12; Aschbacher–Smith A.3.18, printed pp.51–53,
and the consumed prime-rank restriction in 4.3.12(2), p.617. The source
application is in NonblockEndgameSieveModelsNoncubicUnitary.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped MatrixGroups
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.NoncubicPrimeRank
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

private theorem standard_rank_le_one_of_split (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {q : ℕ} (hq : 1 < q) (hF : Nat.card F = q^2)
    (hfix : Nat.card {x : F // J.conj x = x} = q)
    (ho : Odd p) (hd : p ∣ q - 1) :
    primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨_,_,_,_,_,_,ht,_,hG,_⟩ := huppert_II_10_12 J q hF hfix hJ
  obtain ⟨R,H,_,_,_,_,_,hcyc,_,_,_,hH,_⟩ := ht
  let := hcyc
  have hdiv : Nat.gcd (q+1) 3 ∣ q^2-1 := by
    exact (Nat.gcd_dvd_left (q+1) 3).trans (by
      have he : q^2-1 = (q-1)*(q+1) := by
        simpa [Nat.mul_comm] using (Nat.sq_sub_sq q 1)
      rw [he]
      exact dvd_mul_left _ _)
  have hi : H.index = (q^3+1)*q^3 := by
    have hh := H.card_mul_index
    rw [hH,hG, Nat.gcd_comm 3 (q+1), Nat.mul_div_assoc _ hdiv] at hh
    apply Nat.eq_of_mul_eq_mul_left (show 0 < (q^2-1) / Nat.gcd (q+1) 3 by
      rw [← hH]; exact Nat.card_pos)
    rw [hh]
    ring
  have hp := (Fact.out : p.Prime)
  have hqmod : (q : ZMod p) = 1 := by
    have hh := (ZMod.natCast_eq_zero_iff (q-1) p).mpr hd
    rw [Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  have hnot : ¬ p ∣ (q^3+1)*q^3 := by
    intro hh
    have hz := (ZMod.natCast_eq_zero_iff ((q^3+1)*q^3) p).mpr hh
    have ht : (2 : ZMod p) = 0 := by simpa [hqmod, one_add_one_eq_two] using hz
    have htwo := (ZMod.natCast_eq_zero_iff 2 p).mp ht
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo
    subst p
    norm_num at ho
  let P : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J) := default
  exact P.primeRank_le_one_of_isCyclic
    (Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.sylow_isCyclic_of_cyclic_index
      H (by rwa [hi]) P)

/-- Away from q+1, nondefining odd primes have rank at most one in PSU₃(q). -/
theorem projective_rank_le_one (J : HermitianForm 3 F) {q : ℕ}
    (hq : 1 < q) (hF : Nat.card F = q^2)
    (hfix : Nat.card {x : F // J.conj x = x} = q)
    (ho : Odd p) (hpq : ¬ p ∣ q) (hnorm : ¬ p ∣ q+1) :
    primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_cases hd : p ∣ q-1
  · obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hF hfix
    rw [primeRank_congr p e]
    exact standard_rank_le_one_of_split (FormTransport.standardForm J) rfl hq hF hfix ho hd
  · have hsplit : ¬ p ∣ Nat.card F - 1 := by
      rw [hF, show q^2-1 = (q-1)*(q+1) by simpa [Nat.mul_comm] using Nat.sq_sub_sq q 1]
      exact (Fact.out : p.Prime).not_dvd_mul hd hnorm
    have hcard : ¬ p ∣ Nat.card F := by
      rw [hF]
      exact fun hh => hpq ((Fact.out : p.Prime).dvd_of_dvd_pow hh)
    let := Fintype.ofFinite F
    let r := ringChar F
    let : Fact r.Prime := ⟨CharP.char_is_prime F r⟩
    have hpF : (p : F) ≠ 0 :=
      ((isUnit_iff_not_dvd_char F p).mpr (fun hh => hcard
        (by simpa only [Nat.card_eq_fintype_card] using (prime_dvd_char_iff_dvd_card p).mp hh))).ne_zero
    obtain ⟨i,hi⟩ := J.exists_injective_projectiveSpecialLinear
    exact (Theory.GroupTheory.primeRank_le_of_injective p i hi).trans
      (Matrix.PSL3.NonsplitPrimeRank.projective_rank_le_one F r hcard hpF hsplit)

/-- The same bound holds in the full special cover away from the cubic center. -/
theorem special_rank_le_one (J : HermitianForm 3 F) {q : ℕ}
    (hq : 1 < q) (hF : Nat.card F = q^2)
    (hfix : Nat.card {x : F // J.conj x = x} = q)
    (ho : Odd p) (hp3 : p ≠ 3) (hpq : ¬ p ∣ q) (hnorm : ¬ p ∣ q+1) :
    primeRank p J.specialSubgroup ≤ 1 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hk : Nat.Coprime p (Nat.card J.specialToProjective.ker) :=
    Nat.Coprime.of_dvd_right J.card_specialToProjective_ker_dvd_three
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd =>
        hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hd)))
  rw [primeRank_eq_of_surjective_of_coprime p J.specialToProjective J.specialToProjective_surjective hk]
  exact projective_rank_le_one J hq hF hfix ho hpq hnorm
end BenderSuzuki.MatrixGroups.HermitianForm.NoncubicPrimeRank
