module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.SylowTransport
public import Theory.SpecificGroups.AlternatingSix.M10.Action.DegreeTen.SylowModel
public import Theory.SpecificGroups.AlternatingSix.M10.Action.DegreeTen.Words
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The intrinsic degree-ten, three-transitive action of the specified M₁₀

Ten explicit nine-groups supply ten distinct Sylow three-subgroups. Checked
words in three inner generators and the literal `rotation * transposition`
send a fixed ordered triple to every ordered triple of distinct labels.
There are 10·9·8 = 720 such triples, exactly the proved order of the extension.
Their chosen moving elements are therefore all its elements. Sylow conjugacy
then shows that the ten labeled Sylow subgroups exhaust the intrinsic carrier.
The same words prove three-transitivity of its actual conjugation action.

Both exported conclusions have no additional mathematical premises and feed
`M10.actionFacts_of_sylowAction`, including its literal normalizer quotient.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), following 4.8 and the degree-ten action used in 4.10, pp.41–42.
-/

namespace AlternatingSix.M10.Action
open DegreeTen

private def base : Fin 3 ↪ Fin 10 where
  toFun := ![9,0,1]
  inj' := by decide

private theorem sharp (label : Fin 10 → Sylow 3 extension) (hi : Function.Injective label)
    (ht : ∀ x : Fin 3 ↪ Fin 10, ∃ g : extension,
      ∀ i, g • label (base i) = label (x i)) :
    Nat.card (Sylow 3 extension) = 10 ∧
    MulAction.IsMultiplyPretransitive extension (Sylow 3 extension) 3 := by
  classical
  choose move hm using ht
  have hmi : Function.Injective move := by
    intro x y hxy
    apply Function.Embedding.ext
    intro i
    apply hi
    rw [← hm x i, ← hm y i, hxy]
  have hc : Nat.card (Fin 3 ↪ Fin 10) = Nat.card extension := by
    rw [card_extension, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    norm_num [Nat.descFactorial]
  have hms := ((Nat.bijective_iff_injective_and_card move).mpr ⟨hmi, hc⟩).2
  have hs : Function.Surjective label := by
    intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq extension (label (base 0)) P
    obtain ⟨x, rfl⟩ := hms g
    exact ⟨x 0, (hm x 0).symm.trans hg⟩
  let e : Fin 10 ≃ Sylow 3 extension := Equiv.ofBijective label ⟨hi, hs⟩
  constructor
  · rw [← Nat.card_congr e, Nat.card_fin]
  · constructor
    intro x y
    let xx : Fin 3 ↪ Fin 10 := x.trans e.symm.toEmbedding
    let yy : Fin 3 ↪ Fin 10 := y.trans e.symm.toEmbedding
    have hx (i : Fin 3) : move xx • label (base i) = x i := by
      rw [hm]
      exact e.apply_symm_apply (x i)
    have hy (i : Fin 3) : move yy • label (base i) = y i := by
      rw [hm]
      exact e.apply_symm_apply (y i)
    refine ⟨move yy * (move xx)⁻¹, ?_⟩
    apply Function.Embedding.ext
    intro i
    change (move yy * (move xx)⁻¹) • x i = y i
    rw [mul_smul, ← hx i, inv_smul_smul, hy]

private noncomputable def wordElement (w : List (Fin 4)) : extension :=
  (w.map generator).prod

private theorem wordElement_smul (w : List (Fin 4)) (i : Fin 10) :
    wordElement w • label i = label (wordPermutation w i) := by
  induction w with
  | nil => simp [wordElement, wordPermutation]
  | cons k w ih =>
    change (generator k * wordElement w) • label i =
      label ((permutation k * wordPermutation w) i)
    rw [mul_smul, ih, generator_smul]
    rfl

private theorem triple_moves (x : Fin 3 ↪ Fin 10) : ∃ g : extension,
    ∀ i, g • label (base i) = label (x i) := by
  have h01 : x 0 ≠ x 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (x.injective h)
  have h02 : x 0 ≠ x 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (x.injective h)
  have h12 : x 1 ≠ x 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (x.injective h)
  obtain ⟨h0, h1, h2⟩ := tripleWord_spec (x 0) (x 1) (x 2) h01 h02 h12
  refine ⟨wordElement (tripleWord (x 0) (x 1) (x 2)), ?_⟩
  intro i
  rw [wordElement_smul]
  apply congrArg label
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem sylowFacts : Nat.card (Sylow 3 extension) = 10 ∧
    MulAction.IsMultiplyPretransitive extension (Sylow 3 extension) 3 :=
  sharp label label_injective triple_moves

/-- The specified extension has exactly ten Sylow three-subgroups. -/
public theorem card_sylowThree : Nat.card (Sylow 3 extension) = 10 :=
  sylowFacts.1

/-- Conjugation by the specified extension is three-transitive on its Sylow
three-subgroups. -/
public theorem sylowThree_threeTransitive :
    MulAction.IsMultiplyPretransitive extension (Sylow 3 extension) 3 :=
  sylowFacts.2

end AlternatingSix.M10.Action
