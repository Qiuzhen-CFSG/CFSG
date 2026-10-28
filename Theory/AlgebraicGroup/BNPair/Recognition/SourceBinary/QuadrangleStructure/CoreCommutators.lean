module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commuting opposite roots inside an abelian parabolic core

The two roots U_i and U_i^{s_j}, for distinct i and j, lie in the same
literal complementary intersection U_{s_j}. The earlier local-kernel
containment makes that intersection normal in the full j-parabolic, hence
contained in its two-core. An abelian two-core therefore makes the two
roots commute. This uses the actual marked quotient and both original
simple reflections, including arbitrary lifts in its full normalizer.

This is the structural shortcut from the stronger elementary-core conclusion
of DGS (10.5) to the commuting clause of Fong-Seitz I (6A)(a), printed p.37.
It also applies to the abelian-core side of (6A)(b). No model identification,
perfectness, or root-commutator conclusion is included in the hypotheses.
The local-kernel containment is the earlier section 2/5 premise, not (6A).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)

private theorem simple_sq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem first_lengths (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 := by
  have h1 (b : Bool) := wordLength_alternatingWord Q b (n := 1)
    (by have := rotationOrder_ge_two Q; omega)
  have h2 (b : Bool) := wordLength_alternatingWord Q b (n := 2) (rotationOrder_ge_two Q)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one] using And.intro (h1 false) (h2 false)
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one] using And.intro (h1 true) (h2 true)
  · exact (hij rfl).elim

/-- Both roots lie in the same complementary intersection, in either orientation. -/
theorem opposite_roots_le_remainder (i j : Fin 2) (hij : i ≠ j) :
    simpleRoot Q split i ≤ simpleRemainder Q split j ∧
      rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split j := by
  have hi := first_lengths Q i j hij
  have hj := first_lengths Q j i hij.symm
  constructor
  · exact simpleRoot_le_ascent_intersection Q split (Q.simple j) i (by rw [hj.1, hj.2])
  · apply rootAt_le_remainder Q split i j (Q.simple j)
    · rw [simple_inv, hj.2, hj.1]
    · rw [simple_inv, simple_sq, one_mul, hi.1, Q.tits.wordLength_one]

/-- Relative normality puts the literal complementary section in the full local two-core. -/
theorem remainder_le_parabolic_core (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    simpleRemainder Q split i ≤ (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 :=
  le_pCoreIn_of_normalizes
    (split.isTwo.of_injective (inclusion (show simpleRemainder Q split i ≤ split.U from
      inf_le_left)) (inclusion_injective _))
    (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _)))
    (remainder_parabolic_normalizes Q split i hV)

/-- A full parabolic core inside U also lies in its conjugate by the simple reflection. -/
theorem parabolic_core_le_remainder (i : Fin 2)
    (hU : (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 ≤ split.U) :
    (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 ≤ simpleRemainder Q split i := by
  let A := Q.tits.standardParabolic {Q.simple i}
  let n := representative (Q.simple i)
  have hn : (n : X ⧸ Q.D) ∈ A :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  have hnorm : A ≤ normalizer (A.pCoreIn 2 : Set (X ⧸ Q.D)) := by
    intro a ha
    apply le_normalizer_map A.subtype
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top]
    trivial
  apply le_inf hU
  intro x hx
  exact hU ((mem_normalizer_iff.mp (hnorm hn) x).mp hx)

/-- The earlier kernel containment makes the complementary section exactly the local two-core. -/
theorem remainder_eq_parabolic_core (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hU : (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 ≤ split.U) :
    simpleRemainder Q split i = (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 :=
  le_antisymm (remainder_le_parabolic_core Q split i hV)
    (parabolic_core_le_remainder Q split i hU)


/-- The actual two roots commute when the containing parabolic core is abelian. -/
theorem root_commutator_eq_bot_of_abelian_core (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split j ≤ localKernel Q j)
    (hcore : IsMulCommutative ((Q.tits.standardParabolic {Q.simple j}).pCoreIn 2)) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  obtain ⟨hA,hB⟩ := opposite_roots_le_remainder Q split i j hij
  have hR := remainder_le_parabolic_core Q split j hV
  exact bot_unique ((commutator_mono (hA.trans hR) (hB.trans hR)).trans
    (commutator_self_eq_bot_iff.mpr hcore).le)

/-- The same identity for any supplied representative of the original simple reflection.
Right conjugation is implemented by comap under Lean's left conjugation. -/
theorem root_commutator_eq_bot_of_abelian_core_lift (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split j ≤ localKernel Q j)
    (hcore : IsMulCommutative ((Q.tits.standardParabolic {Q.simple j}).pCoreIn 2))
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple j) :
    ⁅simpleRoot Q split i, rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)⁆ = ⊥ := by
  rw [← rootAt_eq Q split i (Q.simple j) n hn]
  exact root_commutator_eq_bot_of_abelian_core Q split i j hij hV hcore

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
