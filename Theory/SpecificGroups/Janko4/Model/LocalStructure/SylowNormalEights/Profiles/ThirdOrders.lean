module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Candidates
public import Theory.GroupTheory.BinaryCollection.Subsequence

/-!
# Orders of the proposed third lower-central terms

Each displayed sequence is a subsequence of the canonical generators and is
triangular under the literal presentation relations. Uniqueness of the full
normal forms, obtained from the order hypothesis, gives uniqueness on each
subsequence. Binary collection then proves the orders 128, 1024, and 512.

The small kernel checks below inspect only generator supports and list
inclusion. They do not enumerate the group or assert any centralizer or
commutator equality. The latter identities are consumed separately in
`Profiles.centralizerProfiles_of_candidates`.

Source: the proposed sequences in `SylowNormalEights/source/profile-data.json`,
with provenance and conventions in its adjacent README.
-/

public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
open Theory.GroupTheory.BinaryCollection

private theorem triangular_of_support (l : List (Fin 21))
    (hord : l.Pairwise (· < ·))
    (hs : ∀ a ∈ l, ∀ j ∈ squareWord a, j ∈ l ∧ a < j)
    (hc : ∀ a ∈ l, ∀ b ∈ l, a < b → ∀ j ∈ conjugateWord a b, j ∈ l ∧ a < j) :
    triangular (l.map generator) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    obtain ⟨hlt, hord⟩ := List.pairwise_cons.mp hord
    have ht (b : Fin 21) (hb : b ∈ a :: l) (j : Fin 21)
        (hj : j ∈ a :: l) (hbj : b < j) : j ∈ l := by
      have hab : a ≤ b := by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_refl _
        · exact le_of_lt (hlt b hb)
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · exact hj
    apply triangular_cons_of_words generator a l (squareWord a) (conjugateWord a)
      (generator_relations.square a)
      (fun b hb => generator_relations.conjugate a b (hlt b hb))
    · intro j hj
      have h := hs a List.mem_cons_self j hj
      exact ht a List.mem_cons_self j h.1 h.2
    · intro b hb j hj
      have h := hc a List.mem_cons_self b (List.mem_cons_of_mem a hb) (hlt b hb) j hj
      exact ht a List.mem_cons_self j h.1 h.2
    · apply ih hord
      · intro b hb j hj
        have h := hs b (List.mem_cons_of_mem a hb) j hj
        exact ⟨ht b (List.mem_cons_of_mem a hb) j h.1 h.2, h.2⟩
      · intro b hb c hc' hbc j hj
        have h := hc b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc') hbc j hj
        exact ⟨ht b (List.mem_cons_of_mem a hb) j h.1 h.2, h.2⟩

private theorem third_support : ∀ i : Fin 3,
    (thirdIndices i).Pairwise (· < ·) ∧
    (∀ a ∈ thirdIndices i, ∀ j ∈ squareWord a, j ∈ thirdIndices i ∧ a < j) ∧
    (∀ a ∈ thirdIndices i, ∀ b ∈ thirdIndices i, a < b →
      ∀ j ∈ conjugateWord a b, j ∈ thirdIndices i ∧ a < j) := by
  have hord : ∀ i : Fin 3, (thirdIndices i).Pairwise (· < ·) := by decide +kernel
  have hs : ∀ (i : Fin 3) (a : Fin 21), a ∈ thirdIndices i →
      ∀ j ∈ squareWord a, j ∈ thirdIndices i ∧ a < j := by decide +kernel
  have hc : ∀ (i : Fin 3) (a b : Fin 21), a ∈ thirdIndices i → b ∈ thirdIndices i → a < b →
      ∀ j ∈ conjugateWord a b, j ∈ thirdIndices i ∧ a < j := by
    intro i
    fin_cases i <;> decide +kernel
  exact fun i => ⟨hord i, hs i, fun a ha b hb hab => hc i a b ha hb hab⟩

/-- The displayed sequences collect using the original presentation relations. -/
theorem third_triangular (i : Fin 3) : triangular ((thirdIndices i).map generator) :=
  triangular_of_support _ (third_support i).1 (third_support i).2.1 (third_support i).2.2

/-- The proposed third terms have the asserted orders, independently of their
identification with the full-centralizer commutator terms. -/
theorem thirdCandidate_card (hcard : Nat.card Carrier = 2 ^ 21) (i : Fin 3) :
    Nat.card (thirdCandidate i) = profileOrder i := by
  have hsub : ((thirdIndices i).map generator).Sublist (List.ofFn generator) := by
    change ((thirdIndices i).map generator).Sublist ((List.finRange 21).map generator)
    exact ((by decide +kernel : ∀ i : Fin 3,
      (thirdIndices i).Sublist (List.finRange 21)) i).map generator
  have hinj : Function.Injective
      (fun n : Fin (2 ^ (List.ofFn generator).length) => product (List.ofFn generator) n.val) := by
    intro n m h
    have he := (normalForm_bijective_of_card hcard).injective
      (a₁ := ⟨n.val, by simpa only [List.length_ofFn] using n.isLt⟩)
      (a₂ := ⟨m.val, by simpa only [List.length_ofFn] using m.isLt⟩) h
    exact Fin.ext (congrArg Fin.val he)
  have h := card_closure_of_sublist hsub (third_triangular i) hinj
  change Nat.card (Subgroup.closure {x | x ∈ (thirdIndices i).map generator}) = _
  rw [h]
  exact (by decide +kernel : ∀ i : Fin 3,
    2 ^ ((thirdIndices i).map generator).length = profileOrder i) i

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
