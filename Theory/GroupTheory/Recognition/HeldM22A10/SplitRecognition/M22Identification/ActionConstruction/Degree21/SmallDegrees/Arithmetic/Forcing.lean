module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic.Supports
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Rows

/-!
# Forced constituent rows and the small-degree consequences

Apply the checked triple certificates to the actual supports of an arbitrary
finite integer system. First force the third induction, then the first, and
finally the second using compatibility with both. These rows exclude degree
twenty and identify every possible degree-twenty-one coefficient vector.
The degree equations also force constituents of degrees 99 and 210.
Source: Janko (1968), Sections 6--7, the assertions on p.16.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
open CharacterOrder
variable {J : Type*} [Fintype J] (S : DegreeSystem J)

private theorem actual_row_mem (j : J) (hj : j ≠ S.principal) :
    (S.degree j, fun l => S.coefficient l j) ∈ rows :=
  row_mem _ _ (degree_le S j) (S.divides j) (fun l => S.unit l j)
    (S.restriction j) (S.fixed_nonnegative j) (S.faithful j hj)

private theorem force (i : Fin 3) (R F : List SignedRow)
    (hlocal : ∀ j ∈ support S (i.castLE (by decide)),
      signed (i.castLE (by decide)) (S.degree j, fun l => S.coefficient l j) ∈ R)
    (hcheck : ∀ {a b c}, a ∈ R → b ∈ R → c ∈ R →
      Triple (i.castLE (by decide)) a b c → a ∈ F)
    (j : J) (hj : j ∈ support S (i.castLE (by decide))) :
    signed (i.castLE (by decide)) (S.degree j, fun l => S.coefficient l j) ∈ F := by
  classical
  obtain ⟨b, c, hjb, hjc, hbc, hs⟩ := support_triple_at S i j hj
  have hb : b ∈ support S (i.castLE (by decide)) := by rw [hs]; simp
  have hc : c ∈ support S (i.castLE (by decide)) := by rw [hs]; simp
  exact hcheck (hlocal j hj) (hlocal b hb) (hlocal c hc)
    (support_equations S i hjb hjc hbc hs)

private theorem decode_two : ∀ r ∈ rows, signed 2 r ∈ forced2 →
    r = (55, ![0,-1,1,0,0]) ∨ r = (154, ![1,1,1,1,0]) ∨
      r = (210, ![0,0,-1,0,1]) := by decide +kernel
private theorem decode_zero : ∀ r ∈ rows, signed 0 r ∈ forced0 →
    r = (231, ![1,0,0,0,0]) ∨ r = (385, ![-1,0,0,1,0]) ∨
      r = (154, ![1,1,1,1,0]) := by decide +kernel
private theorem decode_one : ∀ r ∈ rows, signed 1 r ∈ forced1 →
    r = (55, ![0,-1,1,0,0]) ∨ r = (154, ![1,1,1,1,0]) ∨
      r = (99, ![0,-1,0,0,-1]) := by decide +kernel

public theorem third_constituents (j : J) (hj : j ≠ S.principal)
    (hc : S.coefficient 2 j ≠ 0) :
    (S.degree j, fun l => S.coefficient l j) = (55, ![0,-1,1,0,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (154, ![1,1,1,1,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (210, ![0,0,-1,0,1]) := by
  apply decode_two _ (actual_row_mem S j hj)
  apply force S 2 signedRows2 forced2 ?_ (fun ha hb hc h => triple_two ha hb hc h) j
    ((mem_support S 2 j).mpr ⟨hj, hc⟩)
  intro l hl
  obtain ⟨hlp, hlc⟩ := (mem_support S 2 l).mp hl
  exact signed_mem_two _ (actual_row_mem S l hlp) hlc

private theorem third_degrees (j : J) (hj : j ≠ S.principal) :
    S.coefficient 2 j = 0 ∨ S.degree j = 55 ∨ S.degree j = 154 ∨ S.degree j = 210 := by
  by_cases hc : S.coefficient 2 j = 0
  · exact Or.inl hc
  right
  rcases third_constituents S j hj hc with h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (congrArg Prod.fst h))

public theorem first_constituents (j : J) (hj : j ≠ S.principal)
    (hc : S.coefficient 0 j ≠ 0) :
    (S.degree j, fun l => S.coefficient l j) = (231, ![1,0,0,0,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (385, ![-1,0,0,1,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (154, ![1,1,1,1,0]) := by
  apply decode_zero _ (actual_row_mem S j hj)
  apply force S 0 signedRows0 forced0 ?_ (fun ha hb hc h => triple_zero ha hb hc h) j
    ((mem_support S 0 j).mpr ⟨hj, hc⟩)
  intro l hl
  obtain ⟨hlp, hlc⟩ := (mem_support S 0 l).mp hl
  exact signed_mem_zero _ (actual_row_mem S l hlp) hlc (third_degrees S l hlp)

public theorem second_constituents (j : J) (hj : j ≠ S.principal)
    (hc : S.coefficient 1 j ≠ 0) :
    (S.degree j, fun l => S.coefficient l j) = (55, ![0,-1,1,0,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (154, ![1,1,1,1,0]) ∨
    (S.degree j, fun l => S.coefficient l j) = (99, ![0,-1,0,0,-1]) := by
  apply decode_one _ (actual_row_mem S j hj)
  apply force S 1 finalRows1 forced1 ?_ (fun ha hb hc h => triple_one ha hb hc h) j
    ((mem_support S 1 j).mpr ⟨hj, hc⟩)
  intro l hl
  obtain ⟨hlp, hlc⟩ := (mem_support S 1 l).mp hl
  apply signed_mem_one_final _ (actual_row_mem S l hlp) hlc (third_degrees S l hlp)
  by_cases h0 : S.coefficient 0 l = 0
  · exact Or.inl h0
  · exact Or.inr (first_constituents S l hlp h0)

public theorem no_twenty (j : J) : S.degree j ≠ 20 := by
  intro hd
  have hj : j ≠ S.principal := by intro h; rw [h, S.principal_degree] at hd; omega
  have hs := small_rows _ _ (S.positive j) (S.divides j) (show S.degree j ≤ 21 by omega)
    (fun i => S.unit i j) (S.fixed_nonnegative j) (S.faithful j hj) (S.restriction j)
  rcases hs with ⟨_, hc | hc⟩ | ⟨hn, _⟩
  · have he := congrFun hc 2
    simp at he
    rcases third_degrees S j hj with h | h | h | h <;> omega
  · have he := congrFun hc 0
    simp at he
    have hn : S.coefficient 0 j ≠ 0 := by omega
    rcases first_constituents S j hj hn with h | h | h <;>
      have hh := congrArg Prod.fst h <;> dsimp at hh <;> omega
  · omega

public theorem twenty_one_row (j : J) (hd : S.degree j = 21) :
    (fun i => S.coefficient i j) = ![0,0,0,1,-1] := by
  have hj : j ≠ S.principal := by intro h; rw [h, S.principal_degree] at hd; omega
  have hs := small_rows _ _ (S.positive j) (S.divides j) (show S.degree j ≤ 21 by omega)
    (fun i => S.unit i j) (S.fixed_nonnegative j) (S.faithful j hj) (S.restriction j)
  rcases hs with ⟨hn, _⟩ | ⟨_, hc | hc⟩
  · omega
  · exact hc
  · have he := congrFun hc 2
    simp at he
    rcases third_degrees S j hj with h | h | h | h <;> omega


public theorem exists_degree_210 :
    ∃ j : J, (S.degree j, fun l => S.coefficient l j) = (210, ![0,0,-1,0,1]) := by
  classical
  by_contra! hn
  let d (j : J) : ℤ := (signed 2 (S.degree j, fun l => S.coefficient l j)).1
  have hd (j : J) (hj : j ∈ support S 2) : d j = 55 ∨ d j = 154 := by
    obtain ⟨hjp, hjc⟩ := (mem_support S 2 j).mp hj
    rcases third_constituents S j hjp hjc with h | h | h
    · left
      have he := congrArg (fun r : Row => (signed 2 r).1) h
      simpa [d, signed] using he
    · right
      have he := congrArg (fun r : Row => (signed 2 r).1) h
      simpa [d, signed] using he
    · exact (hn j h).elim
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := support_triple S 2
  change support S 2 = {a, b, c} at hs
  have ha : a ∈ support S 2 := by rw [hs]; simp
  have hb : b ∈ support S 2 := by rw [hs]; simp
  have hc : c ∈ support S 2 := by rw [hs]; simp
  have he := (support_equations S 2 hab hac hbc hs).1
  change d a + d b + d c = targetDegree 2 at he
  simp [targetDegree, exceptionalCoefficients] at he
  rcases hd a ha with h1 | h1 <;> rcases hd b hb with h2 | h2 <;>
    rcases hd c hc with h3 | h3 <;> omega

public theorem exists_degree_99 :
    ∃ j : J, (S.degree j, fun l => S.coefficient l j) = (99, ![0,-1,0,0,-1]) := by
  classical
  by_contra! hn
  let d (j : J) : ℤ := (signed 1 (S.degree j, fun l => S.coefficient l j)).1
  have hd (j : J) (hj : j ∈ support S 1) : d j = -55 ∨ d j = 154 := by
    obtain ⟨hjp, hjc⟩ := (mem_support S 1 j).mp hj
    rcases second_constituents S j hjp hjc with h | h | h
    · left
      have he := congrArg (fun r : Row => (signed 1 r).1) h
      simpa [d, signed] using he
    · right
      have he := congrArg (fun r : Row => (signed 1 r).1) h
      simpa [d, signed] using he
    · exact (hn j h).elim
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := support_triple S 1
  change support S 1 = {a, b, c} at hs
  have ha : a ∈ support S 1 := by rw [hs]; simp
  have hb : b ∈ support S 1 := by rw [hs]; simp
  have hc : c ∈ support S 1 := by rw [hs]; simp
  have he := (support_equations S 1 hab hac hbc hs).1
  change d a + d b + d c = targetDegree 1 at he
  simp [targetDegree, exceptionalCoefficients] at he
  rcases hd a ha with h1 | h1 <;> rcases hd b hb with h2 | h2 <;>
    rcases hd c hc with h3 | h3 <;> omega

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
