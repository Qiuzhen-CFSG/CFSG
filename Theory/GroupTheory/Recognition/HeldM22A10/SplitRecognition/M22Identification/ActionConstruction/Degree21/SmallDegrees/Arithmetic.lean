module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic.Forcing

/-!
# Excluding degree twenty and repeated degree twenty-one rows

The first three exceptional inductions force their constituent rows by a
checked finite calculation. If two degree-21 indices existed, they and the
forced degree-99 and degree-210 indices would use four of the five places in
the fifth induction. Its remaining signed degree would be -69, contrary to
degree divisibility. Numerical rows are never assumed to determine indices.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Sections 6--7, the minimum-degree and uniqueness assertions on p.16.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open CharacterOrder
namespace Arithmetic
variable {J : Type*} [Fintype J] (S : DegreeSystem J)

public theorem unique_twenty_one (a b : J) (ha : S.degree a = 21) (hb : S.degree b = 21) :
    a = b := by
  classical
  by_contra hab
  obtain ⟨u, hu⟩ := exists_degree_99 S
  obtain ⟨v, hv⟩ := exists_degree_210 S
  have huD : S.degree u = 99 := congrArg Prod.fst hu
  have hvD : S.degree v = 210 := congrArg Prod.fst hv
  have hau : a ≠ u := by intro h; subst u; omega
  have hav : a ≠ v := by intro h; subst v; omega
  have hbu : b ≠ u := by intro h; subst u; omega
  have hbv : b ≠ v := by intro h; subst v; omega
  have huv : u ≠ v := by intro h; subst v; omega
  have haC : S.coefficient 4 a = -1 := by
    have h := congrFun (twenty_one_row S a ha) 4
    simpa using h
  have hbC : S.coefficient 4 b = -1 := by
    have h := congrFun (twenty_one_row S b hb) 4
    simpa using h
  have huC : S.coefficient 4 u = -1 := by
    have h := congrFun (congrArg Prod.snd hu) 4
    simpa using h
  have hvC : S.coefficient 4 v = 1 := by
    have h := congrFun (congrArg Prod.snd hv) 4
    simpa using h
  let t : Finset J := {a, b, u, v}
  have ht : t.card = 4 := by simp [t, hab, hau, hav, hbu, hbv, huv]
  have hsub : t ⊆ support S 4 := by
    intro j hj
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    all_goals
      apply (mem_support S 4 _).mpr
      constructor
    · intro h; rw [h, S.principal_degree] at ha; omega
    · rw [haC]; decide
    · intro h; rw [h, S.principal_degree] at hb; omega
    · rw [hbC]; decide
    · intro h; rw [h, S.principal_degree] at huD; omega
    · rw [huC]; decide
    · intro h; rw [h, S.principal_degree] at hvD; omega
    · rw [hvC]; decide
  have hcard : (support S 4 \ t).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, support_card_five S, ht]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  let f (j : J) : ℤ := S.coefficient 4 j * (S.degree j : ℤ)
  have hsum : ∑ j ∈ support S 4, f j = 0 := by
    have h := sum_support S 4 f (by intro j hj; simp [f, hj])
    simpa [f, S.principal_coefficient,
      exceptionalCoefficients, S.degree_zero] using h
  have htSum : ∑ j ∈ t, f j = 69 := by
    simp [t, f, hab, hau, hav, hbu, hbv, huv, ha, hb, huD, hvD, haC, hbC, huC, hvC]
  have he := Finset.sum_sdiff (f := f) hsub
  rw [hw, Finset.sum_singleton, htSum, hsum] at he
  have hn : S.degree w = 69 := by
    dsimp [f] at he
    rcases S.unit 4 w with h | h | h <;> rw [h] at he <;> omega
  have hdiv := S.divides w
  rw [hn] at hdiv
  norm_num at hdiv

end Arithmetic

/-- The pure finite arithmetic input required by `minimum_and_unique_of_arithmetic`.
It applies to the complete family and uses no character-table or recognition premise. -/
public theorem degreeSystem_excludes_twenty_and_unique_twenty_one
    {J : Type*} [Fintype J] (S : DegreeSystem J) :
    (∀ j, S.degree j ≠ 20) ∧
    (∀ j l, S.degree j = 21 → S.degree l = 21 → j = l) :=
  ⟨Arithmetic.no_twenty S, Arithmetic.unique_twenty_one S⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
