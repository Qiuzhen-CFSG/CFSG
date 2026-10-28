module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Consequences
import Mathlib.Tactic.Group

/-!
# Removing the odd defects by a common central twist

Let `z` be the central binary value of the seventh marked word. Reflection
compatibility identifies the eighth value with `z`. Multiplying all three
marked involutions by `z` preserves every even equation and kills entries
7 and 8. The generic checked word derivation then supplies entry 9 for this
twisted family, so all twelve literal local relators hold.

This construction does not assert that twisting extends to the whole source
presentation. `BinaryOdd.Splitting` uses only the resulting local map and
its difference character to prove that `z` was already one.

Source: John Bray's ATLAS `Held/Model/Source/HeG1-P1.M`, the frozen words in
`M1Restriction/Data.lean`, and the original checked ninth-word derivation.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open RelatorLifts MappedConsequences

private def twistFamily {E : Type*} [Group E] (h : Presentation →* E)
    (z : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1) : InvolutionFamily E where
  val n := h (conjugate n) * z
  inv_eq n := by
    have hi : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)
    have ha : (h (conjugate n))⁻¹ = h (conjugate n) :=
      inv_eq_of_mul_eq_one_left (by
        simpa only [map_pow, map_one, pow_two, map_mul] using congrArg h (conjugate_sq n))
    rw [mul_inv_rev, hi, ha]
    exact (Subgroup.mem_center_iff.mp hz _).symm

private theorem twist_value {E : Type*} [Group E] (h : Presentation →* E)
    (z : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1) (w : List ℤ) :
    MappedConsequences.value (twistFamily h z hz hs) w =
      h (RelatorLifts.value w) * z ^ w.length := by
  induction w with
  | nil => simp [MappedConsequences.value, RelatorLifts.value]
  | cons n w ih =>
    have hc := Subgroup.mem_center_iff.mp hz (h (RelatorLifts.value w))
    change (h (conjugate n) * z) * MappedConsequences.value (twistFamily h z hz hs) w =
      h (conjugate n * RelatorLifts.value w) * z ^ (w.length + 1)
    rw [ih, map_mul, pow_succ', mul_assoc, ← mul_assoc z, ← hc]
    simp only [mul_assoc]

/-- A common central binary twist kills all twelve marked relations. -/
private theorem twisted_relations {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap) (heven : EvenImageRelations h)
    (z : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)) = z) :
    ∀ i : Fin 12, MappedConsequences.value (twistFamily h z hz hs)
      ((relationIndices i).map markedIndex) = 1 := by
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)
  have he8 : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 8)) = z := by
    rw [image_eight_eq_inverse_seven f h ht (by rw [hseven]; exact hz), hseven, hinv]
  have initial (i : Fin 12) (hi : i.val < 4) :
      h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters i)) = 1 := by
    rw [initial_relations i hi, map_one]
  have he5 := image_five_of_four h (heven 4 (Or.inl rfl))
  have he6 := heven 6 (Or.inr (Or.inl rfl))
  have he10 := heven 10 (Or.inr (Or.inr (Or.inl rfl)))
  have he11 := heven 11 (Or.inr (Or.inr (Or.inr rfl)))
  have values (i : Fin 14) : h (RelatorLifts.value (localWords i)) =
      if i = 7 ∨ i = 8 then z else 1 := by
    fin_cases i
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using initial 0 (by decide)
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using initial 1 (by decide)
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using initial 2 (by decide)
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using initial 3 (by decide)
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using heven 4 (Or.inl rfl)
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he5
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he6
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using hseven
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he8
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he10
    · simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he11
    · exact image_value_neg_eq_one f h ht _ (by simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he6)
    · exact image_value_neg_eq_one f h ht _ (by simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he10)
    · exact image_value_neg_eq_one f h ht _ (by simpa [relation_eq_value, localWords, relationIndices, markedIndex] using he11)
  have hr : Relations (twistFamily h z hz hs) := by
    intro i
    rw [twist_value, values, pow_eq_pow_mod _ hs]
    fin_cases i <;> simp [localWords, ← pow_two, hs]
  intro i
  fin_cases i
  · exact hr 0
  · exact hr 1
  · exact hr 2
  · exact hr 3
  · exact hr 4
  · exact hr 5
  · exact hr 6
  · exact hr 7
  · exact hr 8
  · exact ninth_of_relations hr
  · exact hr 9
  · exact hr 10
private theorem marked_twist_value {E : Type*} [Group E]
    (h : Presentation →* E) (z : E) (hz : z ∈ Subgroup.center E)
    (hs : z ^ 2 = 1) (w : List (Fin 3)) :
    Subgroup.CosetWordCertificate.eval (fun i => h (liftedGenerator i) * z)
      (w.map (fun i => (i, true))) =
        MappedConsequences.value (twistFamily h z hz hs) (w.map markedIndex) := by
  induction w with
  | nil => simp [MappedConsequences.value]
  | cons i w ih =>
    rw [List.map_cons, Subgroup.CosetWordCertificate.eval_cons]
    change (h (liftedGenerator i) * z) *
        Subgroup.CosetWordCertificate.eval (fun i => h (liftedGenerator i) * z)
          (w.map (fun i => (i, true))) =
      (h (conjugate (markedIndex i)) * z) *
        MappedConsequences.value (twistFamily h z hz hs) (w.map markedIndex)
    rw [ih, liftedGenerator_eq_conjugate]

/-- Literal local relators hold after twisting the three marked lifts by the
central seventh defect. The even-image hypotheses are unchanged. -/
theorem twisted_image_relations {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap) (heven : EvenImageRelations h)
    (z : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)) = z) :
    ∀ i : Fin 12, Subgroup.CosetWordCertificate.eval
      (fun j => h (liftedGenerator j) * z) (relationLetters i) = 1 := by
  intro i
  rw [relationLetters, marked_twist_value h z hz hs]
  exact twisted_relations f h ht heven z hz hs hseven i

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
