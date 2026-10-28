module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup

/-!
# Small-word tools for the interval lower bound

The last three generators form a normal tail. Ascending representatives for
the envelope modulo that tail use seven binary coordinates. These are literal
word identities in the universal presentation; no order assumption is needed.
The lower-bound proof uses normality to recover the core from an element whose
first surviving coordinate is g16.

Source: the triangular presentation in SylowNormalEights/PresentationData;
Aschbacher–Smith A.3.12, pp.47–48, and the adjacent source provenance.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

/-- Closure of the indicated canonical generators. -/
def span (l : List (Fin 21)) : Subgroup Carrier :=
  Subgroup.closure {x | x ∈ l.map generator}

theorem span_le_iff (l : List (Fin 21)) (N : Subgroup Carrier) :
    span l ≤ N ↔ ∀ i ∈ l, generator i ∈ N := by
  rw [span, Subgroup.closure_le]
  constructor
  · intro h i hi
    exact h (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact h i hi

theorem span_eq_words (l : List (Fin 21)) :
    span l = wordSubgroup generator (l.map (fun i => [i])) := by
  apply le_antisymm
  · apply (span_le_iff _ _).mpr
    intro i hi
    have h := (wordSubgroup_le_iff generator (l.map (fun i => [i])) _).mp le_rfl
    simpa using h [i] (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · apply (wordSubgroup_le_iff _ _ _).mpr
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    simpa using (span_le_iff _ _).mp le_rfl i hi

theorem word_mem_span (l w : List (Fin 21)) (h : ∀ i ∈ w, i ∈ l) :
    wordValue w ∈ span l := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact (span_le_iff l (span l)).mp le_rfl i (h i hi)

def tail : Subgroup Carrier := span [18,19,20]
def repWord (n : Fin 128) : List (Fin 21) := selectWord [9,11,13,14,15,16,17] n.val
def tailWord (n : Fin 8) : List (Fin 21) := selectWord [18,19,20] n.val
def envelopeWord (n : Fin 1024) : List (Fin 21) :=
  selectWord [9,11,13,14,15,16,17,18,19,20] n.val

theorem envelope_eq_span : envelope = span [9,11,13,14,15,16,17,18,19,20] :=
  (span_eq_words [9,11,13,14,15,16,17,18,19,20]).symm

theorem core_eq_span : core = span [16,18,19,20] :=
  (span_eq_words [16,18,19,20]).symm

theorem tailWord_mem (n : Fin 8) : wordValue (tailWord n) ∈ tail :=
  word_mem_span [18,19,20] (tailWord n)
    ((by decide +kernel : ∀ n : Fin 8, ∀ i ∈ tailWord n, i ∈ [18,19,20]) n)

private theorem normal_span_of_collect (l : List (Fin 21)) (fuel : ℕ)
    (h : ∀ (j i : Fin 21), i ∈ l →
      ∀ k ∈ collect fuel (inverseGeneratorWord j ++ [i,j]), k ∈ l) : (span l).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← show Subgroup.closure (Set.range generator) = ⊤ from
    PresentedGroup.closure_range_of _]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  suffices hh : (generator j)⁻¹ ∈ Subgroup.normalizer (span l) by
    exact inv_mem_iff.mp hh
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hle : span l ≤ (span l).comap (MulAut.conj (generator j)⁻¹) := by
    apply (span_le_iff _ _).mpr
    intro i hi
    change (generator j)⁻¹ * generator i * ((generator j)⁻¹)⁻¹ ∈ span l
    have he := collect_sound fuel (inverseGeneratorWord j ++ [i,j])
    simp only [wordValue_append, wordValue_inverseGeneratorWord, wordValue_cons,
      wordValue_nil, mul_one, ← mul_assoc] at he
    rw [inv_inv, ← he]
    exact word_mem_span l _ (h j i hi)
  exact hle hx

instance tail_normal : tail.Normal :=
  normal_span_of_collect [18,19,20] 100 (by decide +kernel)

theorem tail_triangular : Theory.GroupTheory.BinaryCollection.triangular
    (([18, 19, 20] : List (Fin 21)).map generator) := by
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 18
    [19, 20] (squareWord 18) (conjugateWord 18)
    (generator_relations.square 18) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 18 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [19, 20] → (18 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 19
    [20] (squareWord 19) (conjugateWord 19)
    (generator_relations.square 19) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 19 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [20] → (19 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 20
    [] (squareWord 20) (conjugateWord 20)
    (generator_relations.square 20) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 20 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [] → (20 : Fin 21) < j) j hj)
  trivial

theorem envelope_triangular : Theory.GroupTheory.BinaryCollection.triangular
    (([9, 11, 13, 14, 15, 16, 17, 18, 19, 20] : List (Fin 21)).map generator) := by
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 9
    [11, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 9) (conjugateWord 9)
    (generator_relations.square 9) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 9 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [11, 13, 14, 15, 16, 17, 18, 19, 20] → (9 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 11
    [13, 14, 15, 16, 17, 18, 19, 20] (squareWord 11) (conjugateWord 11)
    (generator_relations.square 11) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 11 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [13, 14, 15, 16, 17, 18, 19, 20] → (11 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 13
    [14, 15, 16, 17, 18, 19, 20] (squareWord 13) (conjugateWord 13)
    (generator_relations.square 13) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 13 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [14, 15, 16, 17, 18, 19, 20] → (13 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 14
    [15, 16, 17, 18, 19, 20] (squareWord 14) (conjugateWord 14)
    (generator_relations.square 14) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 14 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [15, 16, 17, 18, 19, 20] → (14 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 15
    [16, 17, 18, 19, 20] (squareWord 15) (conjugateWord 15)
    (generator_relations.square 15) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 15 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [16, 17, 18, 19, 20] → (15 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 16
    [17, 18, 19, 20] (squareWord 16) (conjugateWord 16)
    (generator_relations.square 16) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 16 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [17, 18, 19, 20] → (16 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 17
    [18, 19, 20] (squareWord 17) (conjugateWord 17)
    (generator_relations.square 17) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 17 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [18, 19, 20] → (17 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 18
    [19, 20] (squareWord 18) (conjugateWord 18)
    (generator_relations.square 18) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 18 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [19, 20] → (18 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 19
    [20] (squareWord 19) (conjugateWord 19)
    (generator_relations.square 19) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 19 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [20] → (19 : Fin 21) < j) j hj)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 20
    [] (squareWord 20) (conjugateWord 20)
    (generator_relations.square 20) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro j hj
    exact generator_relations.conjugate 20 j
      ((by decide +kernel : ∀ j : Fin 21, j ∈ [] → (20 : Fin 21) < j) j hj)
  trivial

theorem tail_cover (x : Carrier) (hx : x ∈ tail) :
    ∃ n : Fin 8, wordValue (tailWord n) = x := by
  obtain ⟨n, hn, he⟩ := Theory.GroupTheory.BinaryCollection.cover _ tail_triangular x hx
  exact ⟨⟨n, hn⟩, (wordValue_selectWord [18,19,20] n).trans he⟩

theorem envelope_cover (x : Carrier) (hx : x ∈ envelope) :
    ∃ n : Fin 1024, wordValue (envelopeWord n) = x := by
  rw [envelope_eq_span] at hx
  obtain ⟨n, hn, he⟩ := Theory.GroupTheory.BinaryCollection.cover _ envelope_triangular x hx
  exact ⟨⟨n, hn⟩, (wordValue_selectWord [9,11,13,14,15,16,17,18,19,20] n).trans he⟩

def repIndex (n : Fin 1024) : Fin 128 := ⟨n.val % 128, Nat.mod_lt _ (by decide)⟩
def tailIndex (n : Fin 1024) : Fin 8 := ⟨n.val / 128, by have := n.isLt; omega⟩

theorem envelope_split (n : Fin 1024) :
    ∃ r : Fin 128, ∃ t : Fin 8, envelopeWord n = repWord r ++ tailWord t := by
  exact ⟨repIndex n, tailIndex n,
    (by decide +kernel : ∀ n : Fin 1024,
      envelopeWord n = repWord (repIndex n) ++ tailWord (tailIndex n)) n⟩

/-- Delete a known tail factor after a checked collection. -/
theorem strip_tail (N : Subgroup Carrier) (ht : tail ≤ N)
    {x : Carrier} (hx : x ∈ N) (w t : List (Fin 21))
    (hs : ∀ i ∈ t, i ∈ [18,19,20]) (he : x = wordValue (w ++ t)) :
    wordValue w ∈ N := by
  rw [he, wordValue_append] at hx
  exact (N.mul_mem_cancel_right (ht (word_mem_span _ _ hs))).mp hx

theorem product_mod_tail (N : Subgroup Carrier) (ht : tail ≤ N)
    (a b c t : List (Fin 21)) (fuel : ℕ)
    (ha : wordValue a ∈ N) (hb : wordValue b ∈ N)
    (hs : ∀ i ∈ t, i ∈ [18,19,20]) (hc : collect fuel (a ++ b) = c ++ t) :
    wordValue c ∈ N :=
  strip_tail N ht (N.mul_mem ha hb) c t hs
    ((wordValue_append a b).symm.trans (wordValue_eq_of_collect fuel _ _ hc))

theorem conjugate_mod_tail (N : Subgroup Carrier) (hn : N.Normal) (ht : tail ≤ N)
    (a b t : List (Fin 21)) (j : Fin 21) (fuel : ℕ)
    (ha : wordValue a ∈ N)
    (hs : ∀ i ∈ t, i ∈ [18,19,20])
    (hc : collect fuel (inverseGeneratorWord j ++ a ++ [j]) = b ++ t) :
    wordValue b ∈ N := by
  have hm : (generator j)⁻¹ * wordValue a * generator j ∈ N := hn.conj_mem' _ ha _
  apply strip_tail N ht hm b t hs
  have he := wordValue_eq_of_collect fuel _ _ hc
  simpa only [wordValue_append, wordValue_inverseGeneratorWord,
    wordValue_cons, wordValue_nil, mul_one] using he

/-- A collected product of two known members remains in the subgroup. -/
theorem product_word_mem (N : Subgroup Carrier) (a b c : List (Fin 21)) (fuel : ℕ)
    (ha : wordValue a ∈ N) (hb : wordValue b ∈ N)
    (hc : collect fuel (a ++ b) = c) : wordValue c ∈ N := by
  rw [← wordValue_eq_of_collect fuel _ _ hc, wordValue_append]
  exact N.mul_mem ha hb

theorem inv_product_word_mem (N : Subgroup Carrier) (a b c : List (Fin 21)) (fuel : ℕ)
    (ha : wordValue a ∈ N) (hb : wordValue b ∈ N)
    (hc : collect fuel (inverseWord a ++ b) = c) : wordValue c ∈ N := by
  rw [← wordValue_eq_of_collect fuel _ _ hc, wordValue_append, wordValue_inverseWord]
  exact N.mul_mem (N.inv_mem ha) hb

theorem conjugate_word_mem (N : Subgroup Carrier) (hn : N.Normal)
    (a b : List (Fin 21)) (j : Fin 21) (fuel : ℕ) (ha : wordValue a ∈ N)
    (hc : collect fuel (inverseGeneratorWord j ++ a ++ [j]) = b) : wordValue b ∈ N := by
  have he := wordValue_eq_of_collect fuel _ _ hc
  simp only [wordValue_append, wordValue_inverseGeneratorWord,
    wordValue_cons, wordValue_nil, mul_one] at he
  rw [← he]
  exact hn.conj_mem' _ ha _

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
