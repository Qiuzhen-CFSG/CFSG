module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal

/-!
# The central models in A.3.18(3) cannot occur here

The component image in I/O_{3'}(I) is centerless. In contrast, the signed
SL3 models with the displayed congruence have a nonidentity central scalar.
For SL3 this follows from the existing cube-root center calculation. For
SU3, Cauchy supplies a scalar of order three in the field of order q squared;
the congruence q = -1 modulo three makes its norm one and its determinant one.
The remaining three covers have their actual cyclic centers of order three.

Thus the model clause alone excludes both (3a) and (3b), independently of
the latter's additional split-action, cyclic-centralizer and conjugacy clauses.
This is an exclusion lemma, not an assertion of the full A.3.18 alternatives.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18
(printed pp.51--52), 1.1.5(3) (pp.501--503), and 15.3.37 (p.1135).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
open Chapter1.Section02.LocalModels

/-- The positive congruence gives a central element of order three in SL3. -/
theorem linear_center_ne_bot {L : Type*} [Group L] {q : ℕ}
    (h : IsSL L 3 q) (hq : q % 3 = 1) : center L ≠ ⊥ := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let eZ := (centerCongr e).trans
    ((MulEquiv.subgroupCongr (Matrix.PSL3.projection_ker F).symm).trans
      (Matrix.PSL3.projectionKernelEquivThree F (hcard ▸ hq)))
  intro hz
  have hc := Nat.card_congr eZ.toEquiv
  rw [hz] at hc
  norm_num [Nat.card_unique] at hc

/-- The negative congruence gives a nonidentity norm-one central scalar in SU3. -/
theorem unitary_center_ne_bot {L : Type*} [Group L] {q : ℕ}
    (h : IsSU L 3 q) (hq : q % 3 = 2) : center L ≠ ⊥ := by
  obtain ⟨F, hF, hfin, J, hcard, hfrob, ⟨e⟩⟩ := h
  have hd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    have hmod : q ^ 2 % 3 = 1 := by norm_num [Nat.pow_mod, hq]
    omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hd
  have hacube : a ^ 3 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hnorm : J.conj (a : F) * a = 1 := by
    rw [hfrob, ← pow_succ]
    have hdiv : 3 ∣ q + 1 := by omega
    have hh : a ^ (q + 1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp (ha ▸ hdiv)
    exact congrArg Units.val hh
  let d := Matrix.GeneralLinearGroup.scalar (Fin 3) a
  have hdJ : d ∈ J.specialSubgroup := by
    refine ⟨J.scalar_mem_unitary_of_norm_one a hnorm, ?_⟩
    change Matrix.GeneralLinearGroup.det d = 1
    simpa only [d, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using hacube
  let z : J.specialSubgroup := ⟨d, hdJ⟩
  have hz : z ∈ center J.specialSubgroup := by
    have hc : d ∈ center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨a, rfl⟩
    exact mem_center_iff.mpr fun x => Subtype.ext (mem_center_iff.mp hc x.val)
  intro hZ
  have hz1 : z = 1 := by
    have hmem := ((centerCongr e).symm ⟨z, hz⟩).property
    change e.symm z ∈ center L at hmem
    rw [hZ, mem_bot] at hmem
    exact e.symm.injective (by simpa using hmem)
  have ha1 : a = 1 := by
    apply Units.ext
    have he := congrArg (fun x : J.specialSubgroup => x.val.val 0 0) hz1
    simpa [z, d, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar] using he
  simp [ha1] at ha

/-- Both signed special-linear models in A.3.18(3) have nontrivial center. -/
theorem signed_center_ne_bot {L : Type*} [Group L] {q : ℕ} {unitary : Bool}
    (h : IsSLSign L unitary 3 q) (hq : q % 3 = if unitary then 2 else 1) :
    center L ≠ ⊥ := by
  cases unitary with
  | false => exact linear_center_ne_bot h hq
  | true => exact unitary_center_ne_bot h hq

/-- The complete common model clause of A.3.18(3) is impossible for this
ordinary component. This excludes both (3a) and (3b) before using their
additional theta, splitting, centralizer or conjugacy conclusions. -/
theorem no_central_image_model {G : Type*} [Group G] [Finite G]
    {I L : Subgroup G} (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 1 ≤ primeRank 3 L)
    (hm : (∃ (unitary : Bool) (q : ℕ),
        q % 3 = (if unitary then 2 else 1) ∧
          IsSLSign ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) unitary 3 q) ∨
      IsAlternatingCover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) 6 ∨
      IsAlternatingCover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))) 7 ∨
      IsM22Cover ((L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)))) : False := by
  have hr : 1 ≤ primeRank 3 (L.subgroupOf I) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  rcases hm with ⟨unitary, q, hq, hm⟩ | hm | hm | hm
  · exact signed_center_ne_bot hm hq (image_center hcomp hodd hr)
  · exact no_center_three hcomp hodd hr hm.2.1
  · exact no_center_three hcomp hodd hr hm.2.1
  · exact no_center_three hcomp hodd hr hm.2.1

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
