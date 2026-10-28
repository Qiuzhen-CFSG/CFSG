module

public import Theory.SpecificGroups.Held.TwoRank.Coloring.OutsideAction

/-!
# Soundness of the Held coloring checks

The cached outside action is checked against the actual normalizer element.
The original ten polycyclic tables then evaluate each of the 2048 words.
A moved point disproves square one or commutation; no equality test for the
whole symmetric group is assumed. The finite checks are assembled separately.

Source: the literal degree-2058 Held action and G.7.3, printed p.348.
-/

@[expose] public section
namespace Held.TwoRank.Coloring
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-- Evaluation uses the existing checked polycyclic tables. -/
def wordAction (n : Fin 2048) (x : Fin 2058) : Fin 2058 :=
  let y := ExtensionChecks.normalFormAction ⟨n.val % 1024, Nat.mod_lt _ (by decide)⟩ x
  if n.val < 1024 then y else outsideAction y

set_option maxRecDepth 8192 in
theorem wordAction_eq (n : Fin 2048) (x : Fin 2058) :
    wordAction n x = (extensionWord n).val.val x := by
  unfold wordAction
  rw [ExtensionChecks.normalFormAction_eq]
  by_cases hn : n.val < 1024
  · simp only [extensionWord, hn, ↓reduceIte, LocalPairs.innerEmbedding_apply]
  · simp only [extensionWord, hn, ↓reduceIte, Subgroup.coe_mul,
      Equiv.Perm.mul_apply, LocalPairs.innerEmbedding_apply]
    exact outsideAction_eq _

/-- Either the recorded position recovers the index, or its square moves a point. -/
def coverCheck (n : Fin 2048) : Bool :=
  decide (classIndex (position n).1 (position n).2 = n) ||
    decide (wordAction n (wordAction n (squareWitness n)) ≠ squareWitness n)

/-- Equal indices or a witness to noncommutation in the actual action. -/
def separationCheck (c : Fin 64) (i j : Fin 12) : Bool :=
  let n := classIndex c i
  let m := classIndex c j
  decide (n = m) || decide (∃ x : Fin 4,
    wordAction n (wordAction m ⟨x.val, by omega⟩) ≠
      wordAction m (wordAction n ⟨x.val, by omega⟩))

private theorem square_action (n : Fin 2048) (h : extensionWord n ^ 2 = 1)
    (x : Fin 2058) : wordAction n (wordAction n x) = x := by
  simp only [wordAction_eq]
  exact congrArg (fun g : extendedSylow => g.val.val x) (by simpa only [pow_two] using h)

private theorem commuting_actions (n m : Fin 2048)
    (h : Commute (extensionWord n) (extensionWord m)) (x : Fin 2058) :
    wordAction n (wordAction m x) = wordAction m (wordAction n x) := by
  simp only [wordAction_eq]
  exact congrArg (fun g : extendedSylow => g.val.val x) h.eq

theorem index_eq_of_coverCheck (n : Fin 2048) (hc : coverCheck n = true)
    (hs : extensionWord n ^ 2 = 1) : classIndex (position n).1 (position n).2 = n := by
  change (_ || _) = true at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact of_decide_eq_true h
  · exact ((of_decide_eq_true h) (square_action n hs _)).elim

theorem eq_of_separationCheck (c : Fin 64) (i j : Fin 12)
    (hc : separationCheck c i j = true)
    (hh : Commute (extensionWord (classIndex c i)) (extensionWord (classIndex c j))) :
    extensionWord (classIndex c i) = extensionWord (classIndex c j) := by
  change (_ || _) = true at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact congrArg extensionWord (of_decide_eq_true h)
  · obtain ⟨x, hx⟩ := of_decide_eq_true h
    exact (hx (commuting_actions _ _ hh _)).elim

end Held.TwoRank.Coloring
