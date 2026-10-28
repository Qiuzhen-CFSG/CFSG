module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# Eight-bit automizer coordinates and words

The three literal binary actions are the finite actions used to place the
normalizer of the selected elementary eight. XOR homomorphisms are determined
by the eight standard masks, and positive generator words preserve the native
sixteen and the two involution colors. Inverse words use generator orders 2, 2, 4.
The subsequent finite certificate performs a stabilizer-chain argument rather
than enumerating the group of order 1290240.
Source: Kleidman--Wilson (1988), Section 2.1, the elementary-eight branch.
-/

@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer
abbrev Mask := Fin 256

def xor (a b : Mask) : Mask :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt⟩

theorem xor_val (a b : Mask) : (xor a b).val = a.val ^^^ b.val := rfl

@[simp] theorem xor_zero (a : Mask) : xor a 0 = a := by apply Fin.ext; exact Nat.xor_zero _
@[simp] theorem zero_xor (a : Mask) : xor 0 a = a := by apply Fin.ext; exact Nat.zero_xor _
@[simp] theorem xor_self (a : Mask) : xor a a = 0 := by apply Fin.ext; exact Nat.xor_self _
theorem xor_assoc (a b c : Mask) : xor (xor a b) c = xor a (xor b c) :=
  Fin.ext (Nat.xor_assoc _ _ _)
theorem xor_comm (a b : Mask) : xor a b = xor b a := Fin.ext (Nat.xor_comm _ _)
theorem xor_left_comm (a b c : Mask) : xor a (xor b c) = xor b (xor a c) := by
  rw [← xor_assoc, xor_comm a b, xor_assoc]

@[simp] theorem xor_cancel (a b : Mask) : xor a (xor a b) = b := by
  rw [← xor_assoc, xor_self, zero_xor]

def linear (cols : Fin 8 → Mask) (x : Mask) : Mask :=
  (List.ofFn (fun i : Fin 8 => if x.val.testBit i.val then cols i else 0)).foldr xor 0

theorem linear_zero (cols : Fin 8 → Mask) : linear cols 0 = 0 := by
  simp [linear, List.ofFn_succ]

theorem linear_xor (cols : Fin 8 → Mask) (m n : Mask) :
    linear cols (xor m n) = xor (linear cols m) (linear cols n) := by
  have h (l : List (Fin 8)) :
      (l.map (fun i => if (xor m n).val.testBit i.val then cols i else 0)).foldr xor 0 =
      xor ((l.map (fun i => if m.val.testBit i.val then cols i else 0)).foldr xor 0)
      ((l.map (fun i => if n.val.testBit i.val then cols i else 0)).foldr xor 0) := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      simp only [xor_val, Nat.testBit_xor]
      cases hm : m.val.testBit i.val <;> cases hn : n.val.testBit i.val <;>
        simp [xor_assoc, xor_left_comm]
  simpa only [List.map_ofFn, Function.comp_def, linear] using h (List.ofFn (fun i : Fin 8 => i))

def bitBasis : Fin 8 → Mask := ![1,2,4,8,16,32,64,128]

theorem basis_expansion (x : Mask) : linear bitBasis x = x := by
  have h : ∀ x : Mask, linear bitBasis x = x := by decide +kernel
  exact h x

theorem hom_linear {α : Type*} (f : Mask → α) (op : α → α → α) (z : α)
    (h0 : f 0 = z) (hf : ∀ a b, f (xor a b) = op (f a) (f b))
    (cols : Fin 8 → Mask) (x : Mask) :
    f (linear cols x) =
      (List.ofFn (fun i : Fin 8 => if x.val.testBit i.val then f (cols i) else z)).foldr op z := by
  have hfold (l : List Mask) : f (l.foldr xor 0) = (l.map f).foldr op z := by
    induction l with
    | nil => exact h0
    | cons a l ih => simp only [List.foldr_cons, List.map_cons, hf, ih]
  unfold linear
  rw [hfold, List.map_ofFn]
  congr 2
  funext i
  dsimp only [Function.comp_def]
  split <;> simp_all only

/-- An XOR homomorphism is determined by the eight standard bit masks.
The target operation is arbitrary, so the lemma also applies to native group products. -/
theorem hom_ext {α : Type*} (f g : Mask → α) (op : α → α → α) (z : α)
    (hf0 : f 0 = z) (hg0 : g 0 = z)
    (hf : ∀ a b, f (xor a b) = op (f a) (f b))
    (hg : ∀ a b, g (xor a b) = op (g a) (g b))
    (hb : ∀ i, f (bitBasis i) = g (bitBasis i)) : f = g := by
  funext x
  rw [← basis_expansion x, hom_linear f op z hf0 hf, hom_linear g op z hg0 hg]
  simp only [hb]

theorem xor_hom_ext (f g : Mask → Mask)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ a b, f (xor a b) = xor (f a) (f b))
    (hg : ∀ a b, g (xor a b) = xor (g a) (g b))
    (hb : ∀ i, f (bitBasis i) = g (bitBasis i)) : f = g :=
  hom_ext f g xor 0 hf0 hg0 hf hg hb

def generatorColumns : Fin 3 → Fin 8 → Mask := ![![52, 177, 183, 187, 37, 147, 243, 128], ![60, 188, 186, 176, 22, 29, 228, 3], ![2, 1, 13, 8, 189, 101, 74, 128]]
def generator (i : Fin 3) : Mask → Mask := linear (generatorColumns i)

def orbitColor (x : Mask) : Bool := (23428502097111430620708257931032542209539514398619923058733785101740869850728 : ℕ).testBit x.val
def inK (x : Mask) : Bool := (13102572538290735535657239259160234982151785 : ℕ).testBit x.val

def wordAction : List (Fin 3) → Mask → Mask
  | [], x => x
  | i :: w, x => generator i (wordAction w x)

theorem wordAction_append (u v : List (Fin 3)) (x : Mask) :
    wordAction (u ++ v) x = wordAction u (wordAction v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => exact congrArg (generator i) ih

def inverseLetter : Fin 3 → List (Fin 3) := ![[0], [1], [2,2,2]]
def inverseWord : List (Fin 3) → List (Fin 3)
  | [] => []
  | i :: w => inverseWord w ++ inverseLetter i

private theorem generator_inverse : ∀ (i : Fin 3) (x : Mask),
    wordAction (inverseLetter i) (generator i x) = x := by decide +kernel

structure Good (e : Mask → Mask) : Prop where
  zero : e 0 = 0
  map_xor : ∀ x y, e (xor x y) = xor (e x) (e y)
  injective : Function.Injective e
  map_inK : ∀ x, inK (e x) = inK x
  map_color : ∀ x, orbitColor (e x) = orbitColor x

private theorem generator_invariants : ∀ (i : Fin 3) (x : Mask),
    inK (generator i x) = inK x ∧ orbitColor (generator i x) = orbitColor x := by decide +kernel

theorem generator_good (i : Fin 3) : Good (generator i) where
  zero := linear_zero _
  map_xor := linear_xor _
  injective := by
    intro a b h
    have h' := congrArg (wordAction (inverseLetter i)) h
    simpa only [generator_inverse] using h'
  map_inK := fun x => (generator_invariants i x).1
  map_color := fun x => (generator_invariants i x).2

theorem Good.comp {f g : Mask → Mask} (hf : Good f) (hg : Good g) : Good (f ∘ g) where
  zero := by simp only [Function.comp_apply, hg.zero, hf.zero]
  map_xor := by intro x y; simp only [Function.comp_apply, hg.map_xor, hf.map_xor]
  injective := hf.injective.comp hg.injective
  map_inK := by intro x; exact (hf.map_inK (g x)).trans (hg.map_inK x)
  map_color := by intro x; exact (hf.map_color (g x)).trans (hg.map_color x)

theorem good_id : Good id where
  zero := rfl
  map_xor := fun _ _ => rfl
  injective := Function.injective_id
  map_inK := fun _ => rfl
  map_color := fun _ => rfl

theorem word_good (w : List (Fin 3)) : Good (wordAction w) := by
  induction w with
  | nil => exact good_id
  | cons i w ih => exact (generator_good i).comp ih

theorem word_inverse (w : List (Fin 3)) (x : Mask) :
    wordAction (inverseWord w) (wordAction w x) = x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [inverseWord, wordAction_append]
    change wordAction (inverseWord w) (wordAction (inverseLetter i) (generator i (wordAction w x))) = x
    rw [generator_inverse, ih]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer
