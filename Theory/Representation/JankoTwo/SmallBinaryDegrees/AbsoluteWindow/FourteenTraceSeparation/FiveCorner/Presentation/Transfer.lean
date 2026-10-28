module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Certifying a corner presentation using additive coordinates

An injective additive coordinate map, its value at the actual ring identity,
and its intertwining with right multiplication suffice. Spanning by evaluated
words proves ring generation, and zero coordinate polynomials prove the literal
relations. A multiplication table or an unrelated algebra of the same dimension
is not enough. This transfer is used with the fixed Hall--Janko corner below.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Certificate

/-- Evaluate generator letters by repeated right multiplication in coordinates. -/
def runWord {V : Type*} (ops : Fin 9 → V → V) (v : V)
    (w : List (Fin 9)) : V := w.foldl (fun z i => ops i z) v

/-- The coordinate value of a two-generator word, with the same binary encoding
as `Certificate.wordValue`. -/
def runCode {V : Type*} (ops : Fin 9 → V → V) (v : V)
    (i j : Fin 9) (n : ℕ) : V :=
  runWord ops v ((n.bits.dropLast.reverse).map fun b => if b then j else i)

/-- Evaluate exactly the published relation using right multiplication. -/
def runRelation {V : Type*} [AddMonoid V] (ops : Fin 9 → V → V) (v : V)
    (r : Relation) : V := (r.terms.map (runCode ops v r.first r.second)).sum

section Transfer
variable {R V : Type*} [Ring R] [AddCommGroup V]
    (x : Fin 9 → R) (ops : Fin 9 → V → V) (F : R →+ V)
    (hmul : ∀ z i, F (z * x i) = ops i (F z))
include hmul

/-- The order of right multiplication is the order of the original word. -/
theorem map_mul_word (z : R) (w : List (Fin 9)) :
    F (z * (w.map x).prod) = runWord ops (F z) w := by
  induction w generalizing z with
  | nil => simp [runWord]
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    rw [ih, hmul]
    rfl

theorem map_word (w : List (Fin 9)) :
    F (w.map x).prod = runWord ops (F 1) w := by
  simpa only [one_mul] using map_mul_word x ops F hmul 1 w

theorem map_code (i j : Fin 9) (n : ℕ) :
    F (wordValue (x i) (x j) n) = runCode ops (F 1) i j n := by
  simpa only [wordValue, runCode, List.map_map, Function.comp_def, apply_ite]
    using map_word x ops F hmul
      ((n.bits.dropLast.reverse).map fun b => if b then j else i)

theorem map_relation (r : Relation) :
    F (r.value x) = runRelation ops (F 1) r := by
  simp only [Relation.value, runRelation, map_list_sum, List.map_map,
    Function.comp_def, map_code x ops F hmul]

/-- Spanning in faithful additive coordinates proves generation in the ring. -/
theorem closure_eq_top_of_word_span (hinj : Function.Injective F)
    (hspan : ∀ v : V, ∃ ws : List (List (Fin 9)),
      (ws.map (runWord ops (F 1))).sum = v) :
    Subring.closure (Set.range x) = ⊤ := by
  apply (Subring.eq_top_iff' _).mpr
  intro z
  obtain ⟨ws, hw⟩ := hspan (F z)
  have hz : (ws.map (fun w => (w.map x).prod)).sum = z := by
    apply hinj
    simpa only [map_list_sum, List.map_map, Function.comp_def, map_word x ops F hmul]
      using hw
  rw [← hz]
  apply Subring.list_sum_mem
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hy
  apply Subring.list_prod_mem
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  exact Subring.subset_closure (Set.mem_range_self i)

/-- Zero coordinate relations certify the unchanged literal polynomial identities. -/
theorem satisfies_of_relations (hinj : Function.Injective F)
    (hrel : ∀ r ∈ relations, runRelation ops (F 1) r = 0) : Satisfies x := by
  intro r hr
  apply hinj
  rw [map_relation x ops F hmul, hrel r hr, map_zero]

end Transfer
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
