module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRankOneStabilizer
import Mathlib.Tactic.FinCases

/-!
# The six four-groups in the 45-point rectangle

The marked point-stabilizer has eight orbits on the six-bit rectangle.
There are four invariant 45-point subsets containing the marked point and
excluding zero. Constant additive pair counts exclude three of them. The
complement of the surviving set is the disjoint union of six triples, each
the nonzero part of a binary two-space. These two-spaces are intrinsic:
three distinct excluded vectors sum to zero exactly when they form one
of the six triples. Thus every additive symmetry of the 45-point locus
permutes the six four-groups.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4, p.218. This module
establishes the finite geometry used for the quotient action, not its
surjectivity or kernel order.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code shear pairCount)

/-- The 18 vectors outside the marked 45-point fusion locus. -/
def exceptional (x : Code) : Bool :=
  x ∈ ([12,13,20,22,28,31,33,34,35,37,38,39,41,44,50,52,59,60] : List Code)

/-- The nonzero complement of the six exceptional triples. -/
def fused (x : Code) : Bool := x != 0 && !exceptional x

private def representative : Fin 8 → Code := ![0,1,4,8,10,12,32,33]
private def label (x : Code) : Fin 8 :=
  if x = 0 then 0
  else if x >>> 3 = 0 then (if x = 4 then 2 else 1)
  else if x >>> 3 = 4 then (if x &&& 7 = 0 ∨ x &&& 7 = 4 then 6 else 7)
  else if x &&& 7 = 0 ∨ x &&& 7 = x >>> 3 then 3
  else if x &&& 7 = 4 ∨ x &&& 7 = (x >>> 3) ^^^ 4 then 5 else 4
private def path (x : Code) : List (Fin 5) := (![[],[],[2,1],[1],[],[3],[4,2,1],[3,1],[],[0],[],[0],[],[0],[4],[4,0],[2,1],[2,1,0],[2,1,0],[2,1],[2,1],[3,2,1,0],[2,1,0],[3,2,1],[1],[1,0],[1],[1,0],[1],[1,4,0],[1,4],[1,0],[],[],[2,1],[1],[0],[0],[2,1,0],[1,0],[3],[3,0],[3],[2,3],[3],[3,0],[4,3],[3,0],[4,2,1],[4,2,1,0],[4,2,1,0],[2,3,1],[4,2,1],[2,3,1,0],[4,2,1,0],[4,2,1],[3,1],[4,1,0],[3,1],[3,1,0],[3,1],[3,1,0],[4,1],[3,1,0]]) x.toFin

private theorem normal_form : ∀ x : Code,
    (path x).foldl (fun a k => shear k a) x = representative (label x) := by decide

private def selected (m : Fin 8 → Bool) : Finset Code :=
  Finset.univ.filter (fun x => m (label x))
private def good : Fin 8 → Bool := ![false,true,true,true,true,false,true,false]
private def bad₁ : Fin 8 → Bool := ![false,false,true,false,true,true,true,true]
private def bad₂ : Fin 8 → Bool := ![false,false,true,true,true,false,true,true]
private def bad₃ : Fin 8 → Bool := ![false,true,true,false,true,true,true,false]

private theorem candidates : ∀ m : Fin 8 → Bool,
    m 0 = false → m 2 = true → (selected m).card = 45 →
      m = good ∨ m = bad₁ ∨ m = bad₂ ∨ m = bad₃ := by
  have cert : ∀ a b c d e f : Bool,
      let m : Fin 8 → Bool := ![false,a,true,b,c,d,e,f]
      (selected m).card = 45 → m = good ∨ m = bad₁ ∨ m = bad₂ ∨ m = bad₃ := by decide
  intro m h0 h2
  have hm : m = ![false,m 1,true,m 3,m 4,m 5,m 6,m 7] := by
    funext i
    fin_cases i <;> first | exact h0 | exact h2 | rfl
  rw [hm]
  exact cert _ _ _ _ _ _

private theorem good_fused : ∀ x : Code, x ∈ selected good ↔ fused x = true := by decide
private theorem bad₁_test : (12 : Code) ∈ selected bad₁ ∧
    pairCount (selected bad₁) 12 ≠ pairCount (selected bad₁) 4 := by decide
private theorem bad₂_test : (33 : Code) ∈ selected bad₂ ∧
    pairCount (selected bad₂) 33 ≠ pairCount (selected bad₂) 4 := by decide
private theorem bad₃_test : (12 : Code) ∈ selected bad₃ ∧
    pairCount (selected bad₃) 12 ≠ pairCount (selected bad₃) 4 := by decide

private theorem mem_fold (s : Finset Code)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (w : List (Fin 5)) (x : Code) :
    w.foldl (fun a k => shear k a) x ∈ s ↔ x ∈ s := by
  induction w generalizing x with
  | nil => rfl
  | cons k w ih => exact (ih _).trans (h k x)


/-- The checked 45-point orbit census. -/
theorem eq_fused_of_forty_five (s : Finset Code) (h0 : (0 : Code) ∉ s)
    (h4 : (4 : Code) ∈ s) (hcard : s.card = 45)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (hpair : ∀ a ∈ s, pairCount s a = pairCount s 4) :
    ∀ x : Code, x ∈ s ↔ fused x = true := by
  classical
  let m : Fin 8 → Bool := fun i => decide (representative i ∈ s)
  have he : s = selected m := by
    ext x
    have hh := mem_fold s h (path x) x
    rw [normal_form] at hh
    simpa only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
      m, decide_eq_true_eq] using hh.symm
  have h0' : m 0 = false := by
    change decide ((0 : Code) ∈ s) = false
    exact decide_eq_false h0
  have h4' : m 2 = true := by
    change decide ((4 : Code) ∈ s) = true
    exact decide_eq_true h4
  rcases candidates m h0' h4' (he ▸ hcard) with hm | hm | hm | hm
  · rw [he, hm]; exact good_fused
  · have hh := hpair 12 (by rw [he, hm]; exact bad₁_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₁_test.2 hh)
  · have hh := hpair 33 (by rw [he, hm]; exact bad₂_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₂_test.2 hh)
  · have hh := hpair 12 (by rw [he, hm]; exact bad₃_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₃_test.2 hh)

theorem exceptional_iff (x : Code) :
    exceptional x = true ↔ x ≠ 0 ∧ fused x = false := by
  have h : ∀ x : Code, exceptional x = true ↔ x ≠ 0 ∧ fused x = false := by decide
  exact h x

/-- The first two nonzero vectors of the six binary two-spaces. -/
def generators : Fin 6 → Code × Code :=
  ![(12,37),(13,33),(20,38),(22,34),(28,39),(31,35)]

/-- The six actual four-element additive subsets of the rectangle coordinates. -/
def line (i : Fin 6) : Finset Code :=
  {0, (generators i).1, (generators i).2, (generators i).1 ^^^ (generators i).2}

theorem line_card : ∀ i : Fin 6, (line i).card = 4 := by decide

theorem line_zero : ∀ i : Fin 6, (0 : Code) ∈ line i := by decide

theorem line_xor : ∀ (i : Fin 6) (x y : Code),
    x ∈ line i → y ∈ line i → x ^^^ y ∈ line i := by
  intro i x y hx hy
  simp only [line, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    fin_cases i <;> decide

theorem line_exceptional : ∀ (i : Fin 6) (x : Code),
    x ∈ line i → x ≠ 0 → exceptional x = true := by decide

theorem exceptional_unique_line : ∀ x : Code, exceptional x = true →
    ∃! i : Fin 6, x ∈ line i := by
  simp only [ExistsUnique]
  decide

theorem line_injective : Function.Injective line := by
  change ∀ i j : Fin 6, line i = line j → i = j
  decide

theorem exceptional_triple : ∀ x y : Code,
    x ≠ y → exceptional x = true → exceptional y = true →
    exceptional (x ^^^ y) = true →
      ∃ i : Fin 6, ({0,x,y,x ^^^ y} : Finset Code) = line i := by decide

theorem exceptional_nonzero : ∀ x : Code, exceptional x = true → x ≠ 0 := by decide

theorem generators_distinct : ∀ i : Fin 6, (generators i).1 ≠ (generators i).2 := by decide

theorem generators_exceptional : ∀ i : Fin 6,
    exceptional (generators i).1 = true ∧ exceptional (generators i).2 = true ∧
      exceptional ((generators i).1 ^^^ (generators i).2) = true := by decide

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
