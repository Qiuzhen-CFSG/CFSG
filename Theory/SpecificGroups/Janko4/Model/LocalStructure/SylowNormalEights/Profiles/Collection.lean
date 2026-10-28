module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Candidates

/-!
# Checked word collection in the fixed presentation

Adjacent equal letters are replaced by their square word; a decreasing pair
is replaced using the relation `g_b⁻¹ * g_a * g_b` for `b < a`. Every rewrite
preserves evaluation. Iterating for any finite fuel therefore certifies a word
identity whenever the resulting list is the claimed target. No termination,
consistency, or order assumption is needed for this soundness theorem.

Positive inverse words use the fact that all letters in the three nonempty
square words are involutions. The mask adapter proves agreement with the
existing ascending binary normal forms. Commutator certificates use exactly
Mathlib's `a * b * a⁻¹ * b⁻¹` convention.

Source: elementary rewriting of the literal relations in `PresentationData`;
their provenance is recorded in `SylowNormalEights/source/README.md`.
-/

@[expose] public section

open scoped commutatorElement

namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

/-- Evaluation of a positive word in the canonical generators. -/
def wordValue (w : List (Fin 21)) : Carrier := (w.map generator).prod

@[simp] theorem wordValue_nil : wordValue [] = 1 := rfl
@[simp] theorem wordValue_cons (i : Fin 21) (w : List (Fin 21)) :
    wordValue (i :: w) = generator i * wordValue w := rfl
@[simp] theorem wordValue_append (u v : List (Fin 21)) :
    wordValue (u ++ v) = wordValue u * wordValue v := by
  simp only [wordValue, List.map_append, List.prod_append]

/-- One adjacent collection step, using a square or an inverse-conjugate relation. -/
def collectStep : List (Fin 21) → Option (List (Fin 21))
  | [] => none
  | [_] => none
  | a :: b :: l =>
    if a = b then some (squareWord a ++ l)
    else if b < a then some (b :: (conjugateWord b a ++ l))
    else (collectStep (b :: l)).map (a :: ·)

/-- Every individual rewrite is an equality in the presented group. -/
theorem collectStep_sound (u v : List (Fin 21)) (h : collectStep u = some v) :
    wordValue v = wordValue u := by
  induction u using collectStep.induct generalizing v with
  | case1 => simp [collectStep] at h
  | case2 a => simp [collectStep] at h
  | case3 a l =>
    simp only [collectStep, ite_true, Option.some.injEq] at h
    subst v
    rw [wordValue_append]
    change ((squareWord a).map generator).prod * _ = _
    rw [← generator_relations.square a]
    simp only [wordValue_cons, mul_assoc]
  | case4 a b l hab hba =>
    simp only [collectStep, if_neg hab, if_pos hba, Option.some.injEq] at h
    subst v
    rw [wordValue_cons, wordValue_append]
    change generator b * (((conjugateWord b a).map generator).prod * _) = _
    rw [← generator_relations.conjugate b a hba]
    simp only [wordValue_cons, ← mul_assoc, mul_inv_cancel, one_mul]
  | case5 a b l hab hba ih =>
    simp only [collectStep, if_neg hab, if_neg hba] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [wordValue_cons, ih w hw]

/-- Bounded collection. Soundness holds even when the supplied fuel runs out. -/
def collect : ℕ → List (Fin 21) → List (Fin 21)
  | 0, w => w
  | n + 1, w => match collectStep w with
    | none => w
    | some v => collect n v

theorem collect_sound (n : ℕ) (w : List (Fin 21)) : wordValue (collect n w) = wordValue w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [collect]
    split
    · rfl
    · rename_i v h
      exact (ih v).trans (collectStep_sound w v h)

/-- A kernel-checked list equality is a certificate for the corresponding group equality. -/
theorem wordValue_eq_of_collect (n : ℕ) (u v : List (Fin 21)) (h : collect n u = v) :
    wordValue u = wordValue v := (collect_sound n u).symm.trans (congrArg wordValue h)

/-- Select the ascending binary word from a sequence of indices. -/
def selectWord : List (Fin 21) → ℕ → List (Fin 21)
  | [], _ => []
  | a :: l, n => if n % 2 = 0 then selectWord l (n / 2) else a :: selectWord l (n / 2)

theorem wordValue_selectWord (l : List (Fin 21)) (n : ℕ) :
    wordValue (selectWord l n) = Theory.GroupTheory.BinaryCollection.product (l.map generator) n := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [selectWord, List.map_cons, Theory.GroupTheory.BinaryCollection.product]
    split_ifs with h
    · simp only [h, pow_zero, one_mul, ih]
    · have hn : n % 2 = 1 := by omega
      simp only [hn, pow_one, wordValue_cons, ih]

/-- Word for the existing ascending-mask convention. -/
def maskWord (n : Fin (2 ^ 21)) : List (Fin 21) := selectWord (List.finRange 21) n.val

@[simp] theorem wordValue_maskWord (n : Fin (2 ^ 21)) : wordValue (maskWord n) = normalForm n :=
  wordValue_selectWord (List.finRange 21) n.val

/-- Positive inverse word; all letters in every square word are involutions. -/
def inverseGeneratorWord (i : Fin 21) : List (Fin 21) := i :: (squareWord i).reverse

theorem wordValue_inverseGeneratorWord (i : Fin 21) :
    wordValue (inverseGeneratorWord i) = (generator i)⁻¹ := by
  have hj : ∀ j ∈ squareWord i, (generator j)⁻¹ = generator j := by
    intro j hj
    apply inv_eq_iff_mul_eq_one.mpr
    rw [generator_relations.square]
    have hz : squareWord j = [] :=
      (by decide +kernel : ∀ i j : Fin 21, j ∈ squareWord i → squareWord j = []) i j hj
    simp [hz]
  have hr : wordValue (squareWord i).reverse = (wordValue (squareWord i))⁻¹ := by
    simp only [wordValue, List.map_reverse, List.prod_inv_reverse, List.map_map]
    congr 2
    exact List.map_congr_left (fun j h => (hj j h).symm)
  apply eq_inv_of_mul_eq_one_right
  change generator i * (generator i * wordValue (squareWord i).reverse) = 1
  rw [← mul_assoc, generator_relations.square, hr]
  exact mul_inv_cancel _

/-- Invert a positive word using only positive generators. -/
def inverseWord (w : List (Fin 21)) : List (Fin 21) := w.reverse.flatMap inverseGeneratorWord

@[simp] theorem wordValue_inverseWord (w : List (Fin 21)) :
    wordValue (inverseWord w) = (wordValue w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a l ih =>
    change wordValue (((a :: l).reverse).flatMap inverseGeneratorWord) = _
    rw [List.reverse_cons, List.flatMap_append, List.flatMap_singleton]
    change wordValue (inverseWord l ++ inverseGeneratorWord a) = _
    rw [wordValue_append, ih, wordValue_inverseGeneratorWord, wordValue_cons, mul_inv_rev]

/-- Multiply two normal forms with a bounded, checked rewrite certificate. -/
theorem normalForm_mul_of_collect (a b c : Fin (2 ^ 21)) (fuel : ℕ)
    (h : collect fuel (maskWord a ++ maskWord b) = maskWord c) :
    normalForm a * normalForm b = normalForm c := by
  have he := wordValue_eq_of_collect fuel _ _ h
  simpa only [wordValue_append, wordValue_maskWord] using he

/-- Certify a commutator with Mathlib's `a*b*a⁻¹*b⁻¹` convention. -/
theorem normalForm_commutator_of_collect (a b c : Fin (2 ^ 21)) (fuel : ℕ)
    (h : collect fuel (maskWord a ++ maskWord b ++ inverseWord (maskWord a) ++
      inverseWord (maskWord b)) = maskWord c) :
    ⁅normalForm a, normalForm b⁆ = normalForm c := by
  have he := wordValue_eq_of_collect fuel _ _ h
  simpa only [wordValue_append, wordValue_inverseWord, wordValue_maskWord,
    commutatorElement_def] using he

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
