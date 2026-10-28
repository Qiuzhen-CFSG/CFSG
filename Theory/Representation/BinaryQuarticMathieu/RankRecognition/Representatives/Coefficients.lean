module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
public import Mathlib.Order.WellFounded

/-!
# Reading the quartic coefficients on basis vectors

The determinant of two different increasing coordinate quadruples vanishes:
one row is zero. For equal quadruples it is the identity determinant.
Consequently the literal alternating sum in `Basic.lean` returns precisely
its specified coefficient. Permuting the arguments has no effect over F₂.
These symbolic lemmas avoid repeatedly expanding determinant permutations in
finite representative calculations. The coefficient convention is the one in
`BinaryQuarticMathieu/source/README.md`.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Representatives

lemma sorted_eq_of_subset (s t : Fin 4 → Fin 10) (hs : StrictMono s) (ht : StrictMono t)
    (h : ∀ i, ∃ j, t i = s j) : t = s := by
  classical
  choose f hf using h
  have hfi : Function.Injective f := fun a b hab => ht.injective (by rw [hf a, hf b, hab])
  have hfs := Finite.surjective_of_injective hfi
  apply ht.range_inj hs |>.mp
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hf i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := hfs j
    exact ⟨i, hf i⟩

lemma basis_det (k l : Fin 210) :
    Matrix.det (fun i j => basisVector (quadruple k i) (quadruple l j)) =
      if l = k then 1 else 0 := by
  classical
  by_cases h : l = k
  · subst l
    rw [if_pos rfl]
    have hm : (fun i j => basisVector (quadruple k i) (quadruple k j)) = (1 : Matrix (Fin 4) (Fin 4) F) := by
      ext i j
      simp [basisVector, Pi.single_apply, (quadruple_strictMono k).injective.eq_iff, Matrix.one_apply, eq_comm]
    rw [hm, Matrix.det_one]
  · rw [if_neg h]
    have hex : ∃ i, ∀ j, quadruple k i ≠ quadruple l j := by
      by_contra! hn
      exact h (quadruple_injective (sorted_eq_of_subset _ _
        (quadruple_strictMono l) (quadruple_strictMono k) hn)).symm
    obtain ⟨i, hi⟩ := hex
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [basisVector, Ne.symm (hi j)]

lemma alternating_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Form) (v : Fin 4 → U) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, AlternatingMap.zero_apply]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, AlternatingMap.add_apply, ih, Finset.sum_insert hi]

lemma quartic_basis (k : Fin 210) :
    quartic (fun i => basisVector (quadruple k i)) =
      if coefficientWord.testBit k.val then 1 else 0 := by
  classical
  unfold quartic
  rw [alternating_sum_apply]
  have he : ∀ l : Fin 210,
      (if coefficientWord.testBit l.val then
        Matrix.detRowAlternating.compLinearMap (coordinateProjection (quadruple l)) else 0)
          (fun i => basisVector (quadruple k i)) =
        if l = k then (if coefficientWord.testBit k.val then (1 : F) else 0) else 0 := by
    intro l
    by_cases h : coefficientWord.testBit l.val
    · rw [if_pos h]
      change Matrix.det (fun i j => basisVector (quadruple k i) (quadruple l j)) = _
      rw [basis_det]
      by_cases hl : l = k
      · subst l; simp [h]
      · simp [hl]
    · rw [if_neg h]
      by_cases hl : l = k
      · subst l; simp [h]
      · simp [hl]
  simp_rw [he]
  simp

lemma basis_permutation (t : Fin 4 → Fin 10) (k : Fin 210) (p : Fin 4 → Fin 4)
    (hp : Function.Injective p) (ht : ∀ i, t i = quadruple k (p i)) :
    quartic (fun i => basisVector (t i)) =
      if coefficientWord.testBit k.val then 1 else 0 := by
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩
  have he : (fun i => basisVector (t i)) = (fun i => basisVector (quadruple k i)) ∘ e := by
    funext i
    exact congrArg basisVector (ht i)
  rw [he, quartic.map_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;>
    simp [h, CharTwo.neg_eq, quartic_basis]

end BinaryQuarticMathieu.RankRecognition.Representatives
