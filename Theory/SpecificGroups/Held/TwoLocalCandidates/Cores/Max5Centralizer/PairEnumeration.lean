module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Initial

/-!
# Exhaustion of the marked pair images for Held's max5 core

A graph permutation centralizing the actual embedded core transports every
word in its seven inverse generators. Three adjacency tests reduce the
initial 64 possible images of 0 to eight. The zero bin of a three-point
adjacency histogram removes four more. A four-point histogram then matches
each remaining image of 0 to the correct image of 48.

All finite checks reduce against the original actor tables and graph row
masks. The private certificate needs no group-order, simplicity or
centralizer-bound hypothesis. See `PairEnumeration/source/README.md` for
its derivation and an untrusted reproducer.

Source: GLS3 Table 5.3p, the extraspecial core in the Held 2B centralizer;
the retained ATLAS HeG1-max5W1 and HeG1-p2058B0 action.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer.PairEnumeration
open Held.NormalizerGraph

-- Words apply the listed generator indices in increasing application order.
private def word : List (Fin 7) → Fin 2058 → Fin 2058
  | [], x => x
  | j :: js, x => word js (actor j x)

private theorem word_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (js : List (Fin 7)) (x : Fin 2058) :
    word js (σ x) = σ (word js x) := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [word, ← actor_commutes σ hσ j, ih]

private abbrev Mark := Bool × List (Fin 7)

private def mark (a b : Fin 2058) (m : Mark) : Fin 2058 :=
  word m.2 (if m.1 then b else a)

private theorem mark_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (a b : Fin 2058) (m : Mark) :
    mark (σ a) (σ b) m = σ (mark a b m) := by
  unfold mark
  cases m.1 <;> simp only [Bool.false_eq_true, if_false, if_true, word_transport σ hσ]

-- The least significant bit records adjacency to the first marked vertex.
private def signature : List (Fin 2058) → Fin 2058 → ℕ
  | [], _ => 0
  | p :: ps, x => (if Adj x p then 1 else 0) + 2 * signature ps x

private theorem signature_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (ps : List (Fin 2058)) (x : Fin 2058) :
    signature (ps.map σ) (σ x) = signature ps x := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, signature, hσ x p, ih]

private def histogram (ps : List (Fin 2058)) (c : ℕ) : ℕ :=
  (List.finRange 2058).countP (fun x => signature ps x == c)

private theorem histogram_eq (ps : List (Fin 2058)) (c : ℕ) :
    histogram ps c = Nat.card {x : Fin 2058 // signature ps x = c} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  rfl

private theorem histogram_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (ps : List (Fin 2058)) (c : ℕ) :
    histogram (ps.map σ) c = histogram ps c := by
  rw [histogram_eq, histogram_eq]
  symm
  apply Nat.card_congr
  exact Equiv.subtypeEquiv σ (fun x => by rw [signature_transport σ hσ])

private theorem marked_histogram_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (a b : Fin 2058) (ms : List Mark) (c : ℕ) :
    histogram (ms.map (mark (σ a) (σ b))) c = histogram (ms.map (mark a b)) c := by
  have he : ms.map (mark (σ a) (σ b)) = (ms.map (mark a b)).map σ := by
    rw [List.map_map]
    apply List.map_congr_left
    intro m _
    exact mark_transport σ hσ a b m
  rw [he, histogram_transport σ hσ.1]



-- These three tests suffice to reject 56 of the 64 initial second coordinates.
private def edgeCode (x : Fin 2058) : List Bool :=
  ([[1, 3], [1, 3, 4], [1, 2, 3, 6]] : List (List (Fin 7))).map
    (fun js => (rowMask x).testBit (word js x).val)

private theorem edgeCode_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (x : Fin 2058) : edgeCode (σ x) = edgeCode x := by
  unfold edgeCode
  apply List.map_congr_left
  intro js _
  rw [word_transport σ hσ]
  exact Bool.eq_iff_iff.mpr (hσ.1 _ _)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem adjacency_candidates : ∀ b : Fin 2058,
    weight0 b.val = weight0 0 → edgeCode b = edgeCode 0 →
    b = 0 ∨ b = 2 ∨ b = 100 ∨ b = 258 ∨ b = 344 ∨ b = 990 ∨ b = 1117 ∨ b = 1432 := by
  apply allLetters
  decide +kernel

-- Small sublists of the 66 word-marked points found in the initial search.
private def threeMarks : List Mark := [(true, []), (true, [2]), (true, [3])]
private def fourMarks : List Mark := [(false, []), (true, []), (true, [1]), (true, [2])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_three_base : histogram (threeMarks.map (mark 48 0)) 0 = 1057 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_three_2 : histogram (threeMarks.map (mark 48 2)) 0 = 1047 := by
  decide +kernel


set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_three_258 : histogram (threeMarks.map (mark 48 258)) 0 = 1047 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_three_344 : histogram (threeMarks.map (mark 48 344)) 0 = 1047 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_three_1117 : histogram (threeMarks.map (mark 48 1117)) 0 = 1047 := by
  decide +kernel

private theorem image0_four (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) :
    σ 0 = 0 ∨ σ 0 = 100 ∨ σ 0 = 990 ∨ σ 0 = 1432 := by
  have ht := marked_histogram_transport σ hσ 48 0 threeMarks 0
  change histogram (threeMarks.map (mark 48 (σ 0))) 0 = _ at ht
  rw [hist_three_base] at ht
  rcases adjacency_candidates (σ 0) (image0 σ hσ) (edgeCode_transport σ hσ 0) with
    h | h | h | h | h | h | h | h
  · exact Or.inl h
  · rw [h, hist_three_2] at ht; contradiction
  · exact Or.inr (Or.inl h)
  · rw [h, hist_three_258] at ht; contradiction
  · rw [h, hist_three_344] at ht; contradiction
  · exact Or.inr (Or.inr (Or.inl h))
  · rw [h, hist_three_1117] at ht; contradiction
  · exact Or.inr (Or.inr (Or.inr h))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_four_base : histogram (fourMarks.map (mark 48 0)) 0 = 858 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_four_48_990 : histogram (fourMarks.map (mark 48 990)) 0 = 860 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_four_48_1432 : histogram (fourMarks.map (mark 48 1432)) 0 = 860 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_four_334_0 : histogram (fourMarks.map (mark 334 0)) 0 = 860 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem hist_four_334_100 : histogram (fourMarks.map (mark 334 100)) 0 = 860 := by
  decide +kernel

private theorem pair_candidates_proof (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) : PairCandidates σ := by
  have ht := marked_histogram_transport σ hσ 48 0 fourMarks 0
  rw [hist_four_base] at ht
  rcases image48 σ hσ with ha | ha
  · rcases image0_four σ hσ with hb | hb | hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr (Or.inl ⟨ha, hb⟩)
    · rw [ha, hb, hist_four_48_990] at ht; contradiction
    · rw [ha, hb, hist_four_48_1432] at ht; contradiction
  · rcases image0_four σ hσ with hb | hb | hb | hb
    · rw [ha, hb, hist_four_334_0] at ht; contradiction
    · rw [ha, hb, hist_four_334_100] at ht; contradiction
    · exact Or.inr (Or.inr (Or.inl ⟨ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ha, hb⟩))

end Held.TwoLocalCandidates.Cores.Max5Centralizer.PairEnumeration

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer

/-- A permutation preserving the actual Held graph and centralizing the
embedded max5 core has one of these four images of the marked pair `(48,0)`. -/
public theorem pair_candidates (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) :
    PairCandidates σ :=
  PairEnumeration.pair_candidates_proof σ hσ

end Held.TwoLocalCandidates.Cores.Max5Centralizer
