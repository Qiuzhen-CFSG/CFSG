module
public import Mathlib.Data.BitVec
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
/-!
# A checked census of the 21-point rectangle orbit

Five elementary shears form the point stabilizer on binary two-by-three
matrices. A short word takes each of the 64 matrices to one of eight orbit
representatives. A nonzero invariant set containing the marked point and
having size 21 has only four possibilities. Three have unequal additive
pair counts at the marked point and another member, which is impossible
for a transitive linear action. The remaining set is precisely the nonzero
rank-one matrices.

The finite certificates enumerate 64 elements and six Boolean orbit choices;
they are checked by the kernel with `decide`. This is the combinatorial input
to the marked source fusion argument for Aschbacher, *Sporadic Groups* (1994),
40.3, pp.217–218. It does not assume a normalizer identification.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
abbrev Code := BitVec 6
instance : Fintype Code := Fintype.ofEquiv (Fin 64) (BitVec.equivFin (m := 6)).toEquiv.symm

def shear (k : Fin 5) (x : Code) : Code :=
  match k.val with
  | 0 => x ^^^ ((x >>> 3) &&& 7)
  | 1 => x ^^^ ((x &&& 9) <<< 1)
  | 2 => x ^^^ ((x &&& 18) >>> 1)
  | 3 => x ^^^ ((x &&& 9) <<< 2)
  | _ => x ^^^ ((x &&& 18) <<< 1)

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
private def good : Fin 8 → Bool := ![false,true,true,true,false,false,true,false]
private def bad₁ : Fin 8 → Bool := ![false,true,true,false,false,true,true,false]
private def bad₂ : Fin 8 → Bool := ![false,false,true,true,false,false,true,true]
private def bad₃ : Fin 8 → Bool := ![false,false,true,false,false,true,true,true]

def pure (x : Code) : Bool :=
  x != 0 && (((x &&& 7) == 0) || ((x >>> 3) == 0) || ((x &&& 7) == (x >>> 3)))

def pairCount (s : Finset Code) (a : Code) : ℕ :=
  (s.filter (fun b => a ^^^ b ∈ s)).card

private theorem candidates : ∀ m : Fin 8 → Bool,
    m 0 = false → m 2 = true → (selected m).card = 21 →
      m = good ∨ m = bad₁ ∨ m = bad₂ ∨ m = bad₃ := by
  have cert : ∀ a b c d e f : Bool,
      let m : Fin 8 → Bool := ![false,a,true,b,c,d,e,f]
      (selected m).card = 21 → m = good ∨ m = bad₁ ∨ m = bad₂ ∨ m = bad₃ := by decide
  intro m h0 h2
  have hm : m = ![false,m 1,true,m 3,m 4,m 5,m 6,m 7] := by
    funext i
    fin_cases i <;> first | exact h0 | exact h2 | rfl
  rw [hm]
  exact cert _ _ _ _ _ _

private theorem good_pure : ∀ x : Code, x ∈ selected good ↔ pure x = true := by decide
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

/-- Invariance under the marked point stabilizer, size 21, and transitivity
of the linear action force the rank-one locus. Transitivity is used only
through its necessary equality of the indicated additive pair counts. -/
theorem eq_pure_of_twenty_one (s : Finset Code) (h0 : (0 : Code) ∉ s)
    (h4 : (4 : Code) ∈ s) (hcard : s.card = 21)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (hpair : ∀ a ∈ s, pairCount s a = pairCount s 4) :
    ∀ x : Code, x ∈ s ↔ pure x = true := by
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
  · rw [he, hm]; exact good_pure
  · have hh := hpair 12 (by rw [he, hm]; exact bad₁_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₁_test.2 hh)
  · have hh := hpair 33 (by rw [he, hm]; exact bad₂_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₂_test.2 hh)
  · have hh := hpair 12 (by rw [he, hm]; exact bad₃_test.1)
    rw [he, hm] at hh
    exact False.elim (bad₃_test.2 hh)
end Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
