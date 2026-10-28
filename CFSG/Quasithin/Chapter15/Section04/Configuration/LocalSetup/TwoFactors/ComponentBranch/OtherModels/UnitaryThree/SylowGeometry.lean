module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Sylow geometry of the odd-prime unitary-three models

For a prime p congruent to 3 modulo 8, every Sylow two-subgroup of SU₃(p)
and PSU₃(p) has order 32 and cyclic center. The forms here are arbitrary
nondegenerate stored Hermitian forms over a field of order p², with fixed
field of order p; no coordinate or Frobenius hypothesis remains.

A.3.21(b) identifies a standard SU₃ Sylow subgroup with one in GU₂(p).
The determinant of every element in a two-subgroup has order dividing four,
since the exact two-part of p+1 is four. Thus the subgroup lies in the
determinant-four level. Its explicit wreathed construction at height two
gives the order, and A.3.21 gives the cyclic center.
Orthonormalization and finite-field transport identify arbitrary SU models.
Finally, the natural projective map has odd scalar kernel, so its restriction
to a Sylow subgroup, followed by Sylow conjugacy, is a genuine isomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.3.21(b)
and the following paragraph, printed p.55 (PDF p.66), and the component
models in F.6.18(10)–(11), printed pp.309–310 (PDF pp.320–321).
The final theorem supplies exactly `hgeometry` in the two local-involution
assembly theorems of the parent `UnitaryThree` module.
-/

open Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterA.Section03

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels

private theorem gu2_height_two (p : ℕ) [Fact p.Prime] (hp : p % 8 = 3)
    (T : Sylow 2 (ABG.GU2 p 1 (by decide))) : ABG.IsWreathedOfHeight T 2 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hd : 2 ^ 2 ∣ p ^ 1 + 1 := by norm_num; omega
  have hodd : Odd ((p ^ 1 + 1) / 2 ^ 2) := by
    rw [Nat.odd_iff]
    norm_num
    omega
  obtain ⟨P, hP, _⟩ := ABG.SU2Level_wreathed_sylow p 1 hpodd (by decide) 2
    (by decide) hd hodd
  let detU := (GeneralLinearGroup.det (n := Fin 2)
    (R := GaloisField p (2 * 1))).comp (ABG.unitaryForm 2 p 1 (by decide)).unitarySubgroup.subtype
  have hT : (T : Subgroup (ABG.GU2 p 1 (by decide))) ≤ ABG.SU2Level p 1 (by decide) 2 := by
    intro a ha
    rw [ABG.mem_SU2Level_iff_orderOf_dvd]
    change orderOf (detU a) ∣ 2 ^ 2
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_orderOf_dvd_pow ⟨a, ha⟩
    have hd2 : orderOf (detU a) ∣ 2 ^ k :=
      (orderOf_map_dvd detU a).trans (by simpa only [Subgroup.orderOf_mk] using hk)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hdet : orderOf (detU a) ∣ 2 ^ 2 * ((p ^ 1 + 1) / 2 ^ 2) := by
      rw [Nat.mul_div_cancel' hd]
      exact ABG.GU2_det_orderOf_dvd p 1 (by decide) a
    rw [hj] at hdet ⊢
    exact (hodd.coprime_two_left.pow_left j).dvd_mul_right.mp hdet
  let e : T ≃* P := (Subgroup.subgroupOfEquivOfLe hT).symm.trans ((T.subtype hT).equiv P)
  exact ABG.wreathed_equiv e.symm hP

/-- The standard SU₃(p) model has Sylow order 32 and cyclic center. -/
theorem rankThree_unitary_sylow_geometry (p : ℕ) [Fact p.Prime] (hp : p % 8 = 3)
    (T : Sylow 2 (RankThreeSU p)) : Nat.card T = 32 ∧ IsCyclic (Subgroup.center T) := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  let P : Sylow 2 (ABG.GU2 p 1 (by decide)) := Sylow.nonempty.some
  obtain ⟨e⟩ := su3_sylow_equiv_GU2 p hpodd T P
  have hP := gu2_height_two p hp P
  exact ⟨(Nat.card_congr e.toEquiv).trans hP.2.1, su3_sylow_center_cyclic p hpodd T⟩

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The source field cardinalities give an actual equivalence with the
standard SU₃ model used in A.3.21, for every nondegenerate Hermitian form. -/
theorem special_unitary_equiv_rankThree (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    Nonempty (J.specialSubgroup ≃* RankThreeSU p) := by
  apply J.nonempty_specialEquiv_of_card (ABG.unitaryForm 3 p 1 (by decide)) p hcard hfixed
  · exact GaloisField.card p (2 * 1) (by decide)
  · apply HermitianForm.card_fixed_of_prime_frobenius (p := p)
    intro x
    change iterateFrobeniusEquiv (GaloisField p (2 * 1)) p 1 x = x ^ p
    simp only [iterateFrobeniusEquiv_def, pow_one]

/-- Arbitrary-form SU₃ has the same Sylow order and cyclic center. -/
theorem special_unitary_sylow_geometry (p : ℕ) [Fact p.Prime] (hp : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (T : Sylow 2 J.specialSubgroup) : Nat.card T = 32 ∧ IsCyclic (Subgroup.center T) := by
  obtain ⟨e⟩ := special_unitary_equiv_rankThree J p hcard hfixed
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let eT : T ≃* U := e.subgroupMap (T : Subgroup J.specialSubgroup)
  have hU := rankThree_unitary_sylow_geometry p hp U
  exact ⟨(Nat.card_congr eT.toEquiv).trans hU.1, (Subgroup.centerCongr eT).isCyclic.mpr hU.2⟩

/-- Every Sylow two-subgroup of the actual arbitrary-form PSU₃ image has
order 32 and cyclic center when the prime fixed-field order is 3 modulo 8. -/
theorem projective_unitary_sylow_geometry (p : ℕ) [Fact p.Prime] (hp : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card P = 32 ∧ IsCyclic (Subgroup.center P) := by
  let T : Sylow 2 J.specialSubgroup := Sylow.nonempty.some
  let e : T ≃* P := Sylow.equivOfSurjectiveCoprime J.specialToProjective
    J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left T P
  have hT := special_unitary_sylow_geometry J p hp hcard hfixed T
  exact ⟨(Nat.card_congr e.symm.toEquiv).trans hT.1, (Subgroup.centerCongr e).isCyclic.mp hT.2⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
end
