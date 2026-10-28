module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The weight-four orbit of the binary seven-point module

Even permutations act transitively on the thirty-five weight-four words.
A permutation between equal-size supports is corrected, when necessary,
by a transposition fixing the target word. Counting the 128 binary words
then gives the odd orbit size, allowing every two-subgroup to fix a point.

Source application: Aschbacher--Smith, 12.3.4 and the choice of the central
escaping weight-four point before 12.3.12, printed pp.808 and 811.
-/

@[expose] public section
namespace BinarySevenCode

private theorem exists_permutation_e4 (v : EvenWord) (hv : weight v.val = 4) :
    ∃ g : Equiv.Perm (Fin 7), evenRepresentation g v = e4 := by
  classical
  have hc : Fintype.card {i : Fin 7 // v.val i ≠ 0} =
      Fintype.card {i : Fin 7 // e4.val i ≠ 0} := by
    simpa only [Fintype.card_subtype, weight] using hv.trans representative_weights.2.1.symm
  let e := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  apply Subtype.ext
  ext i
  change v.val (e.extendSubtype.symm i) = e4.val i
  have hb : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  apply hb
  constructor
  · intro h
    by_contra h'
    have hn := e.extendSubtype_not_mem (e.extendSubtype.symm i) (by simpa using h)
    exact hn (by simpa using h')
  · intro h
    by_contra h'
    have hn := e.extendSubtype_mem (e.extendSubtype.symm i) h'
    exact hn (by simpa using h)

private theorem exists_alternating_e4 (v : EvenWord) (hv : weight v.val = 4) :
    ∃ a : alternatingGroup (Fin 7), evenRepresentation a.val v = e4 := by
  obtain ⟨g, hg⟩ := exists_permutation_e4 v hv
  by_cases hs : Equiv.Perm.sign g = 1
  · exact ⟨⟨g, hs⟩, hg⟩
  have hs' : Equiv.Perm.sign g = -1 := (Int.units_eq_one_or _).resolve_left hs
  have ht : Equiv.Perm.sign swap34 = -1 := by decide
  refine ⟨⟨swap34 * g, ?_⟩, ?_⟩
  · change Equiv.Perm.sign (swap34 * g) = 1
    rw [map_mul, ht, hs']
    decide
  · rw [map_mul, Module.End.mul_apply, hg]
    apply Subtype.ext
    decide

theorem weight_four_transitive (v w : EvenWord)
    (hv : weight v.val = 4) (hw : weight w.val = 4) :
    ∃ a : alternatingGroup (Fin 7), evenRepresentation a.val v = w := by
  obtain ⟨a, ha⟩ := exists_alternating_e4 v hv
  obtain ⟨b, hb⟩ := exists_alternating_e4 w hw
  refine ⟨b⁻¹ * a, ?_⟩
  change evenRepresentation (b.val⁻¹ * a.val) v = w
  rw [map_mul, Module.End.mul_apply, ha, ← hb, ← Module.End.mul_apply,
    ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

abbrev WeightWord (n : ℕ) := {v : EvenWord // weight v.val = n}

abbrev WeightFourWord := WeightWord 4

instance (n : ℕ) : MulAction (Equiv.Perm (Fin 7)) (WeightWord n) where
  smul g v := ⟨evenRepresentation g v.val, (weight_evenRepresentation g v.val).trans v.property⟩
  one_smul v := by apply Subtype.ext; exact congrArg (fun f => f v.val) evenRepresentation.map_one
  mul_smul g h v := by apply Subtype.ext; exact congrArg (fun f => f v.val) (evenRepresentation.map_mul g h)

theorem card_weightFourWord : Nat.card WeightFourWord = 35 := by
  let e : WeightFourWord ≃ {v : Word // (∑ i, v i = 0) ∧ weight v = 4} :=
    { toFun := fun v => ⟨v.val.val, (mem_evenWords_iff _).mp v.val.property, v.property⟩
      invFun := fun v => ⟨⟨v.val, (mem_evenWords_iff _).mpr v.property.1⟩, v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide
/-- The weight-six words correspond to the seven omitted coordinates. -/
theorem card_weightSixWord : Nat.card (WeightWord 6) = 7 := by
  let e : WeightWord 6 ≃ {v : Word // (∑ i, v i = 0) ∧ weight v = 6} :=
    { toFun := fun v => ⟨v.val.val, (mem_evenWords_iff _).mp v.val.property, v.property⟩
      invFun := fun v => ⟨⟨v.val, (mem_evenWords_iff _).mpr v.property.1⟩, v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

end BinarySevenCode
