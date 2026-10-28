module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.BitCertificates

/-!
# From bit certificates to finite graph geometry

Membership bits give common neighbors; the two-center certificate gives
connectedness of the relevant common-neighbor graphs. The six edge witnesses
cover every vertex, proving the triple common-neighbor assertion, in fact
without restrictions on the third vertex.

Source: Aschbacher–Smith, Lemma F.5.8(2), printed pp. 303–304.
-/

@[expose] public section

namespace OmegaSixThree.OrthogonalityGraph.Certificate

private theorem cover_sound (f : Fin 6 → Fin 117) (j : Fin 117)
    (h : (cover f).getLsbD j = true) :
    ∃ a : Fin 6, (rows (f a)).getLsbD j = true := by
  have aux (l : List (Fin 6)) :
      (l.foldr (fun k b => rows (f k) ||| b) (0 : BitVec 117)).getLsbD j = true →
      ∃ a : Fin 6, (rows (f a)).getLsbD j = true := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.foldr_cons, BitVec.getLsbD_or, Bool.or_eq_true]
      rintro (ha | hl)
      · exact ⟨a, ha⟩
      · exact ih hl
  exact aux _ h

theorem common_neighbor (i j : Fin 117) :
    ∃ r : Fin 117, (rows i).getLsbD r = true ∧ (rows j).getLsbD r = true := by
  refine ⟨root i j, ?_⟩
  simpa only [common, BitVec.getLsbD_and, Bool.and_eq_true] using root_check i j

theorem common_neighbor_centers (i j : Fin 117) (hne : i ≠ j)
    (hn : (rows i).getLsbD j = false) :
    ∃ r s : Fin 117, ((rows i).getLsbD r = true ∧ (rows j).getLsbD r = true) ∧
      ((rows i).getLsbD s = true ∧ (rows j).getLsbD s = true) ∧
      (rows r).getLsbD s = true ∧
      ∀ k : Fin 117, (rows i).getLsbD k = true → (rows j).getLsbD k = true →
        (rows r).getLsbD k = true ∨ (rows s).getLsbD k = true := by
  obtain ⟨hs, hc⟩ := centers_check i j hne hn
  simp only [common, BitVec.getLsbD_and, Bool.and_eq_true] at hs
  refine ⟨root i j, second i j, ?_, hs.1, hs.2, ?_⟩
  · simpa only [common, BitVec.getLsbD_and, Bool.and_eq_true] using root_check i j
  · intro k hik hjk
    have hh := congrArg (fun b : BitVec 117 => b.getLsbD k) hc
    simpa only [common, BitVec.getLsbD_and, BitVec.getLsbD_or, hik, hjk,
      Bool.true_and, Bool.or_eq_true] using hh

theorem edge_common_neighbor (i j k : Fin 117) (hij : (rows i).getLsbD j = true) :
    ∃ r : Fin 117, (rows i).getLsbD r = true ∧ (rows j).getLsbD r = true ∧
      (rows k).getLsbD r = true := by
  obtain ⟨hm, hc⟩ := edge_check i j hij
  have hh : (cover (witness i j)).getLsbD k = true := by
    rw [hc]
    simp only [BitVec.getLsbD_allOnes, k.isLt, decide_true]
  obtain ⟨a, hak⟩ := cover_sound (witness i j) k hh
  have hr := hm a
  simp only [common, BitVec.getLsbD_and, Bool.and_eq_true] at hr
  refine ⟨witness i j a, hr.1, hr.2, ?_⟩
  rw [rows_correct, pairing_symm, ← rows_correct]
  exact hak
end OmegaSixThree.OrthogonalityGraph.Certificate
