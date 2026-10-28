module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Conjugates
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Reflection of the odd marked M₁ relations

The substitution fixing `x` and sending `y` to `y⁻¹` preserves all seven
relations of John Bray's Held presentation. For the last source relation,
short consequences of the commutator relation transform its reflected word
back to a cyclic conjugate of the source word. The private equalities below
record these transformations explicitly; every split, overlap and replacement
is checked in the abstract presentation.

The induced endomorphism exchanges the last two marked M₁ generators. The
inverse of the reflected word for entry 7, rotated by ten letters, is exactly
the word for entry 8. Thus entry 8 reduces to entry 7. This does not prove entry 7 or 9.

Sources: `Held/Model/Source/HeG1-P1.M` and the frozen words in
`M1Restriction/Data.lean`. Word multiplication order is unchanged.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts

private theorem conjugate_inv (n : ℤ) : (conjugate n)⁻¹ = conjugate n :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using conjugate_sq n)

private theorem value_append (u v : List ℤ) : value (u ++ v) = value u * value v := by
  simp only [value, List.map_append, List.prod_append]

private theorem value_reverse (w : List ℤ) : value w.reverse = (value w)⁻¹ := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    rw [List.reverse_cons, value_append, ih]
    simp only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev, conjugate_inv]

private theorem value_rotate (w : List ℤ) (h : value w = 1) (k : Nat) :
    value (w.rotate k) = 1 := by
  simpa only [value, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one h k

private theorem value_mod (w : List ℤ) : value (w.map (· % 7)) = value w := by
  unfold value
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro n hn
  exact (conjugate_mod_seven n).symm

private theorem source_split (i : Fin 4) (shift : ℤ) (flip : Bool) (offset : Nat)
    (l r : List ℤ)
    (hs : ((if flip then (((sourceIndices i).map (· + shift)).map (· % 7)).reverse
      else ((sourceIndices i).map (· + shift)).map (· % 7)).rotate offset) =
        l ++ r.reverse) : value l = value r := by
  have h : value (((sourceIndices i).map (· + shift)).map (· % 7)) = 1 := by
    rw [value_mod, source_value_shift]
  have h' : value (if flip then (((sourceIndices i).map (· + shift)).map (· % 7)).reverse
      else ((sourceIndices i).map (· + shift)).map (· % 7)) = 1 := by
    cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte, value_reverse, h, inv_one]
  have he := value_rotate _ h' offset
  rw [hs, value_append, value_reverse, mul_inv_eq_one] at he
  exact he

private theorem in_context {l r : List ℤ} (h : value l = value r)
    (pre post : List ℤ) : value (pre ++ l ++ post) = value (pre ++ r ++ post) := by
  simp only [value_append, h]

private theorem overlap {l₁ r₁ l₂ r₂ : List ℤ}
    (h₁ : value l₁ = value r₁) (h₂ : value l₂ = value r₂)
    (pre post : List ℤ) (hc : l₁ ++ post = pre ++ l₂) :
    value (r₁ ++ post) = value (pre ++ r₂) := by
  rw [value_append, ← h₁, ← value_append, hc, value_append, h₂, value_append]

-- Generated exact source derivation; no search is trusted by Lean.
private theorem eq0 : value [0, 0] = value [] := by
  simpa only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_two] using conjugate_sq 0

private theorem eq1 : value [1, 1] = value [] := by
  simpa only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_two] using conjugate_sq 1

private theorem eq2 : value [2, 2] = value [] := by
  simpa only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_two] using conjugate_sq 2

private theorem eq3 : value [3, 3] = value [] := by
  simpa only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_two] using conjugate_sq 3

private theorem eq6 : value [6, 6] = value [] := by
  simpa only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_two] using conjugate_sq 6

private theorem eq86 : value [2, 1, 2, 3, 2] = value [1, 0, 1, 2, 1] := by
  have h0 : value [2, 1, 2, 3, 2] = value [1, 0, 1, 2, 1] :=
    source_split 0 0 true 1 _ _ (by decide)
  have hl : value [2, 1, 2, 3, 2] = value [2, 1, 2, 3, 2] := rfl
  have hr : value [1, 0, 1, 2, 1] = value [1, 0, 1, 2, 1] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq91 : value [2, 1, 2, 1, 0, 1] = value [3, 2, 1, 2] := by
  have h0 : value [2, 1, 2, 1, 0, 1] = value [3, 2, 1, 2] :=
    source_split 0 0 true 5 _ _ (by decide)
  have hl : value [2, 1, 2, 1, 0, 1] = value [2, 1, 2, 1, 0, 1] := rfl
  have hr : value [3, 2, 1, 2] = value [3, 2, 1, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq94 : value [3, 2, 3, 4, 3] = value [1, 0, 1, 2, 1] := by
  have h0 : value [3, 2, 3, 4, 3] = value [2, 1, 2, 3, 2] :=
    source_split 0 1 true 1 _ _ (by decide)
  have hl : value [3, 2, 3, 4, 3] = value [3, 2, 3, 4, 3] := rfl
  have hr : value [2, 1, 2, 3, 2] = value [1, 0, 1, 2, 1] :=
    (in_context eq86 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem eq98 : value [4, 3, 2, 3, 2] = value [3, 2, 3, 2, 1] := by
  have h0 : value [4, 3, 2, 3, 2] = value [3, 2, 3, 2, 1] :=
    source_split 0 1 true 4 _ _ (by decide)
  have hl : value [4, 3, 2, 3, 2] = value [4, 3, 2, 3, 2] := rfl
  have hr : value [3, 2, 3, 2, 1] = value [3, 2, 3, 2, 1] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq103 : value [4, 3, 4, 5, 4] = value [1, 0, 1, 2, 1] := by
  have h0 : value [4, 3, 4, 5, 4] = value [3, 2, 3, 4, 3] :=
    source_split 0 2 true 1 _ _ (by decide)
  have hl : value [4, 3, 4, 5, 4] = value [4, 3, 4, 5, 4] := rfl
  have hr : value [3, 2, 3, 4, 3] = value [1, 0, 1, 2, 1] :=
    (in_context eq94 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem eq105 : value [3, 4, 5, 4, 3, 4] = value [4, 3, 2, 3] := by
  have h0 : value [3, 4, 5, 4, 3, 4] = value [4, 3, 2, 3] :=
    source_split 0 2 true 2 _ _ (by decide)
  have hl : value [3, 4, 5, 4, 3, 4] = value [3, 4, 5, 4, 3, 4] := rfl
  have hr : value [4, 3, 2, 3] = value [4, 3, 2, 3] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq112 : value [5, 4, 5, 6, 5] = value [1, 0, 1, 2, 1] := by
  have h0 : value [5, 4, 5, 6, 5] = value [4, 3, 4, 5, 4] :=
    source_split 0 3 true 1 _ _ (by decide)
  have hl : value [5, 4, 5, 6, 5] = value [5, 4, 5, 6, 5] := rfl
  have hr : value [4, 3, 4, 5, 4] = value [1, 0, 1, 2, 1] :=
    (in_context eq103 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem eq121 : value [6, 5, 6, 0, 6] = value [1, 0, 1, 2, 1] := by
  have h0 : value [6, 5, 6, 0, 6] = value [5, 4, 5, 6, 5] :=
    source_split 0 4 true 1 _ _ (by decide)
  have hl : value [6, 5, 6, 0, 6] = value [6, 5, 6, 0, 6] := rfl
  have hr : value [5, 4, 5, 6, 5] = value [1, 0, 1, 2, 1] :=
    (in_context eq112 [] [])
  exact hl.symm.trans (h0.trans hr)

private theorem eq129 : value [1, 0, 1, 2, 1] = value [0, 6, 0, 1, 0] := by
  have h0 : value [0, 6, 0, 1, 0] = value [6, 5, 6, 0, 6] :=
    source_split 0 5 true 1 _ _ (by decide)
  have hl : value [0, 6, 0, 1, 0] = value [0, 6, 0, 1, 0] := rfl
  have hr : value [6, 5, 6, 0, 6] = value [1, 0, 1, 2, 1] :=
    (in_context eq121 [] [])
  exact (hl.symm.trans (h0.trans hr)).symm

/-- The five-letter source consequence is fixed by all seven index shifts. -/
theorem five_letter_shift (k : Fin 7) :
    value (([0, 6, 0, 1, 0] : List ℤ).map (fun n => (n + k.val) % 7)) =
      value [0, 6, 0, 1, 0] := by
  fin_cases k
  · rfl
  · exact eq129
  · exact eq86.trans eq129
  · exact eq94.trans eq129
  · exact eq103.trans eq129
  · exact eq112.trans eq129
  · exact eq121.trans eq129

private theorem eq241 : value [1, 2, 3, 4, 6, 4] = value [0, 5, 1, 0, 6, 0] := by
  have h0 : value [0, 5, 1, 0, 6, 0] = value [1, 2, 3, 4, 6, 4] :=
    source_split 3 4 false 4 _ _ (by decide)
  have hl : value [0, 5, 1, 0, 6, 0] = value [0, 5, 1, 0, 6, 0] := rfl
  have hr : value [1, 2, 3, 4, 6, 4] = value [1, 2, 3, 4, 6, 4] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1420 : value [3, 4, 5, 4, 2, 3, 2, 1] = value [4, 2] := by
  have h0 : value [4, 3, 2, 3, 3, 2, 3, 2] = value [3, 4, 5, 4, 3, 3, 2, 3, 2, 1] :=
    overlap eq105 eq98 [3, 4, 5, 4, 3] [3, 2, 3, 2] (by decide)
  have hl : value [4, 3, 2, 3, 3, 2, 3, 2] = value [4, 2] :=
    ((in_context eq3 [4, 3, 2] [2, 3, 2]).trans ((in_context eq2 [4, 3] [3, 2]).trans (in_context eq3 [4] [2])))
  have hr : value [3, 4, 5, 4, 3, 3, 2, 3, 2, 1] = value [3, 4, 5, 4, 2, 3, 2, 1] :=
    (in_context eq3 [3, 4, 5, 4] [2, 3, 2, 1])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1428 : value [2, 1, 2, 0, 6, 0, 1, 0] = value [3, 2] := by
  have h0 : value [3, 2, 1, 2, 2, 1] = value [2, 1, 2, 0, 6, 0, 1, 0] :=
    overlap eq91 eq129 [2, 1, 2] [2, 1] (by decide)
  have hl : value [3, 2, 1, 2, 2, 1] = value [3, 2] :=
    ((in_context eq2 [3, 2, 1] [1]).trans (in_context eq1 [3, 2] []))
  have hr : value [2, 1, 2, 0, 6, 0, 1, 0] = value [2, 1, 2, 0, 6, 0, 1, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1472 : value [2, 1, 2, 0, 6, 0, 1] = value [3, 2, 0] := by
  have h0 : value [3, 2, 0] = value [2, 1, 2, 0, 6, 0, 1] :=
    overlap eq1428 eq0 [2, 1, 2, 0, 6, 0, 1] [0] (by decide)
  have hl : value [3, 2, 0] = value [3, 2, 0] := rfl
  have hr : value [2, 1, 2, 0, 6, 0, 1] = value [2, 1, 2, 0, 6, 0, 1] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1672 : value [4, 0, 6, 0, 1] = value [3, 4, 5, 4, 0] := by
  have h0 : value [4, 2, 2, 0, 6, 0, 1] = value [3, 4, 5, 4, 2, 3, 3, 2, 0] :=
    overlap eq1420 eq1472 [3, 4, 5, 4, 2, 3] [2, 0, 6, 0, 1] (by decide)
  have hl : value [4, 2, 2, 0, 6, 0, 1] = value [4, 0, 6, 0, 1] :=
    (in_context eq2 [4] [0, 6, 0, 1])
  have hr : value [3, 4, 5, 4, 2, 3, 3, 2, 0] = value [3, 4, 5, 4, 0] :=
    ((in_context eq3 [3, 4, 5, 4, 2] [2, 0]).trans (in_context eq2 [3, 4, 5, 4] [0]))
  exact hl.symm.trans (h0.trans hr)

private theorem eq1745 : value [1, 2, 3, 4, 6, 3, 4, 5, 4, 0] = value [0, 5] := by
  have h0 : value [0, 5, 1, 0, 6, 0, 0, 6, 0, 1] = value [1, 2, 3, 4, 6, 3, 4, 5, 4, 0] :=
    overlap eq241 eq1672 [1, 2, 3, 4, 6] [0, 6, 0, 1] (by decide)
  have hl : value [0, 5, 1, 0, 6, 0, 0, 6, 0, 1] = value [0, 5] :=
    ((in_context eq0 [0, 5, 1, 0, 6] [6, 0, 1]).trans ((in_context eq6 [0, 5, 1, 0] [0, 1]).trans ((in_context eq0 [0, 5, 1] [1]).trans (in_context eq1 [0, 5] []))))
  have hr : value [1, 2, 3, 4, 6, 3, 4, 5, 4, 0] = value [1, 2, 3, 4, 6, 3, 4, 5, 4, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem reflected_last_value : value [0, 1, 2, 3, 4, 6, 3, 4, 5, 4, 0, 5] = 1 := by
  calc
    _ = value [0, 0, 5, 5] := in_context eq1745 [0] [5]
    _ = value [5, 5] := in_context eq0 [] [5, 5]
    _ = 1 := by simpa only [value, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, pow_two] using conjugate_sq 5

private theorem reflected_source_value (i : Fin 4) :
    value ((sourceIndices i).map (fun n => -n)) = 1 := by
  rw [← value_mod]
  fin_cases i
  · exact (source_split 0 4 false 5 _ [] (by decide)).trans rfl
  · exact (source_split 1 4 false 1 _ [] (by decide)).trans rfl
  · exact (source_split 2 6 false 1 _ [] (by decide)).trans rfl
  · exact reflected_last_value

private theorem reflected_relations (i : Fin 7) : relationWord x y⁻¹ i = 1 := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_left
    (by simpa only [relationWord, pow_two] using presentation_relations 0)
  have hy : y ^ 7 = 1 := presentation_relations 1
  fin_cases i
  · exact presentation_relations 0
  · simp only [relationWord, inv_pow, hy, inv_one]
  · have he : x * y⁻¹ = MulAut.conj x ((x * y)⁻¹) := by
      have hxx : x * x = 1 := by simpa only [pow_two] using
        (show x ^ 2 = 1 from presentation_relations 0)
      simp only [MulAut.conj_apply, mul_inv_rev, hx, mul_assoc, hxx, mul_one]
    have hxy : (x * y) ^ 17 = 1 := presentation_relations 2
    simp only [relationWord, he, ← map_pow, inv_pow, hxy, inv_one, map_one]
  · have he : value ((sourceIndices 0).map (fun n => -n)) =
        relationWord x y⁻¹ 3 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, mul_inv_rev, hx, inv_inv]
      group
    exact he.symm.trans (reflected_source_value 0)
  · have he : value ((sourceIndices 1).map (fun n => -n)) =
        relationWord x y⁻¹ 4 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, hx, pow_succ, pow_zero]
      group
    exact he.symm.trans (reflected_source_value 1)
  · have he : value ((sourceIndices 2).map (fun n => -n)) =
        relationWord x y⁻¹ 5 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, hx, pow_succ, pow_zero]
      group
    exact he.symm.trans (reflected_source_value 2)
  · have he : value ((sourceIndices 3).map (fun n => -n)) * (y⁻¹) ^ 7 =
        relationWord x y⁻¹ 6 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, pow_succ, pow_zero]
      group
    rw [inv_pow, hy, inv_one, mul_one] at he
    exact he.symm.trans (reflected_source_value 3)

private def reflectionGenerator : Fin 2 → Presentation
  | 0 => x
  | 1 => y⁻¹

private theorem reflection_relators (r : FreeGroup (Fin 2)) (hr : r ∈ definingRelators) :
    FreeGroup.lift reflectionGenerator r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  rw [map_relationWord]
  simpa only [FreeGroup.lift_apply_of, reflectionGenerator] using reflected_relations i

private def reflection : Presentation →* Presentation :=
  PresentedGroup.toGroup reflection_relators

private theorem reflection_x : reflection x = x := PresentedGroup.toGroup.of reflection_relators
private theorem reflection_y : reflection y = y⁻¹ := PresentedGroup.toGroup.of reflection_relators

private theorem reflection_conjugate (n : ℤ) : reflection (conjugate n) = conjugate (-n) := by
  simp only [conjugate, map_mul, map_inv, map_zpow, reflection_x, reflection_y,
    inv_zpow, zpow_neg]

private theorem reflection_value (w : List ℤ) :
    reflection (value w) = value (w.map (fun n => -n)) := by
  simp only [value, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n hn
  exact reflection_conjugate n

/-- Negating the conjugate indices preserves identities in the source presentation. -/
theorem value_neg_eq_one (w : List ℤ) (h : value w = 1) :
    value (w.map (fun n => -n)) = 1 := by
  have hf := congrArg reflection h
  rw [map_one, reflection_value] at hf
  exact hf

/-- The reflection of source generators carries entry 7 to entry 8. -/
theorem relation_eight_of_seven
    (h : Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7) = 1) :
    Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 8) = 1 := by
  rw [relation_eq_value] at h ⊢
  have hf := value_neg_eq_one _ h
  have hr : value (((relationIndices 7).map markedIndex).map (fun n => -n)).reverse = 1 := by
    rw [value_reverse, hf, inv_one]
  exact value_rotate _ hr 10

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts
