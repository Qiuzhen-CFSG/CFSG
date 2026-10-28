module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.GroupAction.FixedCentralizerRigidity
public import Theory.SpecificGroups.SU3.FixedCentralizerRigidity.Graph

/-!
# Fixed-centralizer rigidity for outer involutions of SU₃ and PSU₃

Every projective outer involution is conjugate to entrywise Hermitian
conjugation. The graph calculation and marked isomorphism transport give
rigidity in PSU₃. For SU₃, the actual scalar kernel is the center and has
order dividing three. Perfectness detects innerness after descent, oddness
lifts all fixed elements, and faithful descent then lifts rigidity.

Source: GLS4, Chapter 4, Lemma 3.4(d1), and its application to a unitary
central cover in Chapter 2, Lemma 13.3.
-/

public section
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The full centralizer of an outer involution and its fixed subgroup has
just the identity and that involution in the actual projective model. -/
theorem projective_outer_fixedCentralizerRigid
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ x, a = MulAut.conj x) : MulAut.FixedCentralizerRigid a := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate n hn hJ hcard hfixed
    (projectiveGraphAut_isEntrywiseConjugation J hJ) a ha houter
  rw [← hc]
  apply (MulAut.fixedCentralizerRigid_congr_iff c _).mpr
  exact FixedRigidity.graph_fixedCentralizer J hJ hn hcard hfixed

/-- Rigidity for the actual SU₃ cover, including its possible order-three
center. No hypothesis about lifting or model automorphism coverage remains. -/
theorem special_outer_fixedCentralizerRigid
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut J.specialSubgroup) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ x, a = MulAut.conj x) : MulAut.FixedCentralizerRigid a := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let f : PerfectCentralCovering.Cover J.specialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := J.specialToProjective
    surjective := J.specialToProjective_surjective
    isPerfect := J.special_isPerfect_of_fixed_card hq hcard hfixed
    ker_le_center := J.specialToProjective_ker_le_center }
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hk : f.toMonoidHom.ker = Subgroup.center J.specialSubgroup :=
    J.specialToProjective_ker_eq_center
      (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  have hodd : Odd (Nat.card f.toMonoidHom.ker) :=
    (by decide : Odd 3).of_dvd_nat J.card_specialToProjective_ker_dvd_three
  apply f.fixedCentralizerRigid_of_odd hk hodd a ha
  apply J.projective_outer_fixedCentralizerRigid hn hJ hcard hfixed (f.autMap hk a)
  · rw [← map_pow, ha, map_one]
  · exact fun hi => houter ((f.autMap_inner_iff hk a).mp hi)

end BenderSuzuki.MatrixGroups.HermitianForm
