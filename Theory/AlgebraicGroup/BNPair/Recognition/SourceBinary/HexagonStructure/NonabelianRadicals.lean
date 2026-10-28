module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Both hexagon radicals are nonabelian

For distinct i,j and rotation order six, U_i, U_i^{s_j} and
U_i^{s_j s_i} lie in U_{s_j}. The last two roots are nontrivial and
disjoint. If U_{s_j} were abelian, U_i would centralize both roots,
so R_i = <U_i,U_i^{s_i}> would centralize U_i^{s_j}. A source lift of
s_i in R_i would therefore fix that root, although it carries it to
the disjoint root U_i^{s_j s_i}. This contradiction works for either
orientation and does not require perfectness or a field-size restriction.

This proves the first paragraph of Fong--Seitz I (6E), printed p.44,
from the canonical split-root coordinates and the earlier Section 5
choice of simple lifts in R_i. The local-type exclusions and the unequal
parameter commutators and irreducible action remain separate obligations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)

private theorem simple_sq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem hexagon_lengths (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 4 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 5 := by
  have h1 (b : Bool) := wordLength_alternatingWord Q b (n := 1) (by omega)
  have h2 (b : Bool) := wordLength_alternatingWord Q b (n := 2) (by omega)
  have h3 (b : Bool) := wordLength_alternatingWord Q b (n := 3) (by omega)
  have h4 (b : Bool) := wordLength_alternatingWord Q b (n := 4) (by omega)
  have h5 (b : Bool) := wordLength_alternatingWord Q b (n := 5) (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have hh := And.intro (h1 false) (And.intro (h2 false)
      (And.intro (h3 false) (And.intro (h4 false) (h5 false))))
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh
  · have hh := And.intro (h1 true) (And.intro (h2 true)
      (And.intro (h3 true) (And.intro (h4 true) (h5 true))))
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh
  · exact (hij rfl).elim

theorem simpleRoot_le_other_remainder (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    simpleRoot Q split i ≤ simpleRemainder Q split j := by
  have hl := hexagon_lengths Q hm j i hij.symm
  exact simpleRoot_le_ascent_intersection Q split (Q.simple j) i (by rw [hl.1, hl.2.1])

theorem exchanged_roots_le_remainder (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split j ∧
    rootAt Q split i (Q.simple j*Q.simple i) ≤ simpleRemainder Q split j := by
  have hi := hexagon_lengths Q hm i j hij
  have hj := hexagon_lengths Q hm j i hij.symm
  constructor
  · apply rootAt_le_remainder Q split i j (Q.simple j)
    · rw [simple_inv, hj.2.1, hj.1]
    · rw [simple_inv, simple_sq, one_mul, hi.1, Q.tits.wordLength_one]
  · apply rootAt_le_remainder Q split i j (Q.simple j*Q.simple i)
    · simp only [mul_inv_rev, simple_inv]
      rw [hi.2.1, hi.2.2.1]
    · simp only [mul_inv_rev, simple_inv, ← mul_assoc]
      rw [hj.2.2.1, hj.2.2.2.1]

theorem exchanged_roots_disjoint (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (rootAt Q split i (Q.simple j))
      (rootAt Q split i (Q.simple j*Q.simple i)) := by
  have hi := hexagon_lengths Q hm i j hij
  apply rootAt_disjoint Q split i (Q.simple j) (Q.simple j*Q.simple i)
  simp only [mul_inv_rev, simple_inv, ← mul_assoc]
  rw [hi.2.2.2.1, hi.2.2.2.2]

theorem radical_commutator_ne_bot (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split i) :
    ⁅simpleRemainder Q split j, simpleRemainder Q split j⁆ ≠ ⊥ := by
  intro habel
  have hc := commutator_eq_bot_iff_le_centralizer.mp habel
  have hUi := simpleRoot_le_other_remainder Q split hm i j hij
  obtain ⟨hA, hB⟩ := exchanged_roots_le_remainder Q split hm i j hij
  have hni : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s.val⁻¹ =
      Q.simple i := by rw [map_inv, s.class_eq, simple_inv]
  have hRC : rankOne Q split i ≤ centralizer (rootAt Q split i (Q.simple j) : Set _) := by
    apply sup_le
    · exact hUi.trans (hc.trans (centralizer_le hA))
    · intro x hx
      rw [rootAt_eq Q split i (Q.simple i) s.val s.class_eq] at hx
      change (s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i at hx
      apply mem_centralizer_iff.mpr
      intro y hy
      have hy' : (s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹ ∈
          rootAt Q split i (Q.simple j*Q.simple i) := by
        rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val⁻¹ hni]
        change (s.val : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹)*
          ((s.val : X ⧸ Q.D)⁻¹)⁻¹ ∈ rootAt Q split i (Q.simple j)
        simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
          (show y ∈ rootAt Q split i (Q.simple j) from hy)
      have he := mem_centralizer_iff.mp (hc (hUi hx)) _ (hB hy')
      apply (MulAut.conj (s.val : X ⧸ Q.D)).injective
      simpa only [map_mul, MulAut.conj_apply] using he
  have hnC := hRC s.mem_rankOne
  have he : rootAt Q split i (Q.simple j*Q.simple i) = rootAt Q split i (Q.simple j) := by
    rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val s.class_eq]
    exact rightConjugate_eq_self _ (centralizer_le_normalizer _ hnC)
  have hd := exchanged_roots_disjoint Q split hm i j hij
  rw [he, disjoint_self] at hd
  exact rootAt_ne_bot Q split i (Q.simple j) hd

theorem both_radical_commutators_ne_bot (hm : rotationOrder Q = 6)
    (s : ∀ i, RootReflection Q split i) :
    ⁅simpleRemainder Q split 0, simpleRemainder Q split 0⁆ ≠ ⊥ ∧
    ⁅simpleRemainder Q split 1, simpleRemainder Q split 1⁆ ≠ ⊥ :=
  ⟨radical_commutator_ne_bot Q split hm 1 0 (by decide) (s 1),
    radical_commutator_ne_bot Q split hm 0 1 (by decide) (s 0)⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
