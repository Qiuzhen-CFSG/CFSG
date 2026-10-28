module
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.Interpretation

/-!
# Small word equations for the long J₃ local relations

The checked operations are inversion, cyclic splitting, contextual rewriting
and overlap of two equations. The later replay uses literal short words and
these structural lemmas, without a coset table or finiteness assumption.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords

/-- Evaluation of the positive alphabet used by the small rewriting trace. -/
def readWord {G : Type*} [Group G] (g : Nat → G) (w : List Nat) : G :=
  (w.map g).prod

@[simp] theorem readWord_nil {G : Type*} [Group G] (g : Nat → G) : readWord g [] = 1 := rfl
@[simp] theorem readWord_cons {G : Type*} [Group G] (g : Nat → G) (a : Nat) (w : List Nat) :
    readWord g (a :: w) = g a * readWord g w := rfl

theorem readWord_append {G : Type*} [Group G] (g : Nat → G) (u v : List Nat) :
    readWord g (u ++ v) = readWord g u * readWord g v := by
  simp [readWord, List.map_append, List.prod_append]

/-- Letter zero is an involution; the other four letters come in inverse pairs. -/
def inverseLetter : Nat → Nat
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | n => n

def inverseWord (w : List Nat) : List Nat := (w.reverse.map inverseLetter)

theorem readWord_inverse {G : Type*} [Group G] (g : Nat → G)
    (hi : ∀ n, g (inverseLetter n) = (g n)⁻¹) (w : List Nat) :
    readWord g (inverseWord w) = (readWord g w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord]
  | cons a w ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, readWord_append, readWord_cons, readWord_nil, mul_one] at *
    rw [ih, hi, mul_inv_rev]

def rotate (w : List Nat) (n : Nat) : List Nat := w.drop n ++ w.take n

theorem readWord_rotate_one {G : Type*} [Group G] (g : Nat → G)
    (w : List Nat) (n : Nat) (h : readWord g w = 1) :
    readWord g (rotate w n) = 1 := by
  rw [rotate, readWord_append, mul_eq_one_comm, ← readWord_append,
    List.take_append_drop]
  exact h

theorem cancel {G : Type*} [Group G] (g : Nat → G)
    (hi : ∀ n, g (inverseLetter n) = (g n)⁻¹) (n : Nat) :
    readWord g [n, inverseLetter n] = readWord g [] := by
  simp [hi]

/-- A split of a rotated source relation supplies one rewriting equation. -/
theorem seed {G : Type*} [Group G] (g : Nat → G)
    (hi : ∀ n, g (inverseLetter n) = (g n)⁻¹)
    (r a b : List Nat) (rev : Bool) (n : Nat)
    (hc : a ++ inverseWord b = rotate (if rev then inverseWord r else r) n)
    (hr : readWord g r = 1) : readWord g a = readWord g b := by
  have ho : readWord g (if rev then inverseWord r else r) = 1 := by
    cases rev <;> simp [readWord_inverse, hi, hr]
  have h := readWord_rotate_one g _ n ho
  rw [← hc, readWord_append, readWord_inverse g hi, mul_inv_eq_one] at h
  exact h

/-- Rewriting in an arbitrary surrounding word. -/
theorem context {G : Type*} [Group G] (g : Nat → G) (p s u v : List Nat)
    (h : readWord g u = readWord g v) :
    readWord g (p ++ u ++ s) = readWord g (p ++ v ++ s) := by
  simp only [readWord_append, h]

/-- The two rewrites of an overlap give a new equality. -/
theorem overlap {G : Type*} [Group G] (g : Nat → G) (p m q u v : List Nat)
    (hr : readWord g (p ++ m) = readWord g u)
    (hs : readWord g (m ++ q) = readWord g v) :
    readWord g (u ++ q) = readWord g (p ++ v) := by
  simp only [readWord_append] at *
  rw [← hr, ← hs, mul_assoc]

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords
