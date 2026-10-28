module
public import Theory.Representation.BinarySevenCode.WeightOrbits

/-!
# Weight-two displacements of weight-six words

Two distinct weight-six binary words differ at exactly their two omitted
coordinates. Transporting one word to the standard representative reduces
the check to the 128 binary words, without enumerating the permutation group.
Thus every nontrivial displacement of a weight-six word has weight two.

Source application: the literal [Z,L_e] seed in Aschbacher--Smith,
completion of 12.3.1, printed pp.811--812.
-/

@[expose] public section
namespace BinarySevenCode

set_option maxRecDepth 4096 in
private theorem standard_weight_six_sub (v : EvenWord)
    (hv : weight v.val = 6) (hne : v ≠ e6) : weight (v - e6).val = 2 := by
  have h : ∀ w : Word, weight w = 6 → w ≠ e6.val → weight (w - e6.val) = 2 := by
    decide
  exact h v.val hv (fun he => hne (Subtype.ext he))

/-- The difference of two distinct weight-six words has weight two. -/
theorem weight_six_sub_of_ne (v w : EvenWord)
    (hv : weight v.val = 6) (hw : weight w.val = 6) (hne : v ≠ w) :
    weight (v - w).val = 2 := by
  obtain ⟨a,ha⟩ := exists_alternating_of_weight_eq w e6
    (hw.trans representative_weights.2.2.symm)
  have hn : evenRepresentation a.val v ≠ e6 := by
    intro he
    have hh := congrArg (evenRepresentation a.val⁻¹) (he.trans ha.symm)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hne hh
  have h := standard_weight_six_sub (evenRepresentation a.val v)
    ((weight_evenRepresentation a.val v).trans hv) hn
  rw [← ha, ← map_sub] at h
  exact (weight_evenRepresentation a.val (v-w)).symm.trans h

/-- Every nontrivial displacement of a weight-six word has weight two. -/
theorem weight_six_displacement (a : Equiv.Perm (Fin 7)) (v : EvenWord)
    (hv : weight v.val = 6) (hne : evenRepresentation a v ≠ v) :
    weight (evenRepresentation a v - v).val = 2 :=
  weight_six_sub_of_ne _ _ ((weight_evenRepresentation a v).trans hv) hv hne

end BinarySevenCode
