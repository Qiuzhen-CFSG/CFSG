module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Collection
public import Mathlib.Data.BitVec

/-!
# Sound Boolean-polynomial collection in the literal presentation

A monomial is a finite bit mask and a polynomial is a sum modulo two.
Adjacent equal and decreasing generator pairs can be rewritten with arbitrary
Boolean coefficients, using the original square and inverse-conjugation
relations. Every bounded symbolic collection preserves evaluation. No
cardinality premise is needed for soundness; full order gives injectivity of
ascending Boolean normal forms when comparing collected coordinates.

This supplies a checker for the coordinate calculations required by the
pointwise exclusion. It does not assert those calculations. Source: the
literal SylowNormalEights presentation; Aschbacher–Smith A.3.12, pp.47–48.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseCalculation.Symbolic
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles
abbrev Monomial := BitVec 42
abbrev Poly := List Monomial

def monomialValue (m v : Monomial) : Bool := m &&& v == m

def polyValue (p : Poly) (v : Monomial) : Bool :=
  p.foldr (fun m a => monomialValue m v ^^ a) false

def toggle (m : Monomial) : Poly → Poly
  | [] => [m]
  | a :: p => if m = a then p else if m < a then m :: a :: p else a :: toggle m p

def add (p q : Poly) : Poly := q.foldr toggle p

def mul (p q : Poly) : Poly :=
  p.foldr (fun m r => add r (q.map (m ||| ·))) []

@[simp] theorem polyValue_nil (v : Monomial) : polyValue [] v = false := rfl
@[simp] theorem polyValue_cons (m : Monomial) (p : Poly) (v : Monomial) :
    polyValue (m :: p) v = (monomialValue m v ^^ polyValue p v) := rfl

@[simp] theorem polyValue_toggle (m : Monomial) (p : Poly) (v : Monomial) :
    polyValue (toggle m p) v = (monomialValue m v ^^ polyValue p v) := by
  induction p with
  | nil => simp [toggle]
  | cons a p ih =>
    by_cases h : m = a
    · subst m; simp [toggle]
    · simp only [toggle, if_neg h]
      split
      · rfl
      simp only [polyValue_cons, ih]
      cases monomialValue m v <;> cases monomialValue a v <;> cases polyValue p v <;> rfl

@[simp] theorem polyValue_add (p q : Poly) (v : Monomial) :
    polyValue (add p q) v = (polyValue p v ^^ polyValue q v) := by
  induction q with
  | nil => simp [add]
  | cons a q ih =>
    change polyValue (toggle a (add p q)) v = _
    rw [polyValue_toggle, ih, polyValue_cons]
    cases polyValue p v <;> cases monomialValue a v <;> cases polyValue q v <;> rfl

private theorem monomialValue_or (a b v : Monomial) :
    monomialValue (a ||| b) v = (monomialValue a v && monomialValue b v) := by
  have split_and : ∀ a b c : Bool, ((a || b) && c) = (a || b) →
      (a && c) = a ∧ (b && c) = b := by decide
  apply Bool.eq_iff_iff.mpr
  simp only [monomialValue, beq_iff_eq, Bool.and_eq_true]
  constructor
  · intro h
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i _
      have hi := congrArg (fun t : Monomial => t.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hi ⊢
      exact (split_and _ _ _ hi).1
    · apply BitVec.eq_of_getLsbD_eq
      intro i _
      have hi := congrArg (fun t : Monomial => t.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hi ⊢
      exact (split_and _ _ _ hi).2
  · rintro ⟨ha, hb⟩
    rw [BitVec.and_or_distrib_right, ha, hb]

private theorem polyValue_map_or (m : Monomial) (p : Poly) (v : Monomial) :
    polyValue (p.map (m ||| ·)) v = (monomialValue m v && polyValue p v) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.map_cons, polyValue_cons, monomialValue_or, ih]
    cases monomialValue m v <;> cases monomialValue a v <;> cases polyValue p v <;> rfl

@[simp] theorem polyValue_mul (p q : Poly) (v : Monomial) :
    polyValue (mul p q) v = (polyValue p v && polyValue q v) := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    change polyValue (add (mul p q) (q.map (a ||| ·))) v = _
    rw [polyValue_add, ih, polyValue_map_or, polyValue_cons]
    cases monomialValue a v <;> cases polyValue p v <;> cases polyValue q v <;> rfl

abbrev Word := List (Fin 21 × Poly)
def atomValue (v : Monomial) (a : Fin 21 × Poly) : Carrier :=
  if polyValue a.2 v then generator a.1 else 1

def value (w : Word) (v : Monomial) : Carrier := (w.map (atomValue v)).prod

def clean (w : Word) : Word := w.filter (fun a => !a.2.isEmpty)

@[simp] theorem value_nil (v : Monomial) : value [] v = 1 := rfl
@[simp] theorem value_cons (a : Fin 21 × Poly) (w : Word) (v : Monomial) :
    value (a :: w) v = atomValue v a * value w v := rfl
@[simp] theorem value_append (u w : Word) (v : Monomial) :
    value (u ++ w) v = value u v * value w v := by
  simp [value, List.map_append, List.prod_append]
@[simp] theorem value_clean (w : Word) (v : Monomial) : value (clean w) v = value w v := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | mk i p =>
      cases p with
      | nil => simpa [clean, atomValue] using ih
      | cons m p => simpa [clean] using congrArg (atomValue v (i, m :: p) * ·) ih

@[simp] theorem value_const (w : List (Fin 21)) (p : Poly) (v : Monomial) :
    value (w.map (fun i => (i, p))) v = if polyValue p v then wordValue w else 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, value_cons, atomValue, ih, wordValue_cons]
    cases polyValue p v <;> simp

private theorem conjugateWord_head (i j : Fin 21) (h : i < j) :
    conjugateWord i j = j :: (conjugateWord i j).tail :=
  (by decide +kernel : ∀ i j : Fin 21, i < j →
    conjugateWord i j = j :: (conjugateWord i j).tail) i j h

private theorem swap (i j : Fin 21) (h : i < j) :
    generator j * generator i = generator i * generator j * wordValue (conjugateWord i j).tail := by
  have hc := generator_relations.conjugate i j h
  change (generator i)⁻¹ * generator j * generator i = wordValue (conjugateWord i j) at hc
  rw [conjugateWord_head i j h, wordValue_cons] at hc
  have hh := congrArg (generator i * ·) hc
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh

def replacement (a b : Fin 21) (p q : Poly) : Word :=
  if a = b then [(a, add p q)] ++ (squareWord a).map (fun i => (i, mul p q))
  else [(b,q), (a,p)] ++ (conjugateWord b a).tail.map (fun i => (i, mul p q))

private theorem replacement_sound (a b : Fin 21) (p q : Poly) (h : b ≤ a) (v : Monomial) :
    value (replacement a b p q) v = atomValue v (a,p) * atomValue v (b,q) := by
  by_cases hab : a = b
  · subst b
    simp only [replacement, ↓reduceIte, value_append, value_cons, value_nil, mul_one,
      value_const, atomValue, polyValue_add, polyValue_mul]
    cases hp : polyValue p v <;> cases hq : polyValue q v <;>
      simp
    exact (generator_relations.square a).symm
  · have hba : b < a := lt_of_le_of_ne h (Ne.symm hab)
    simp only [replacement, if_neg hab, value_append, value_cons, value_nil, mul_one,
      value_const, atomValue, polyValue_mul]
    cases hp : polyValue p v <;> cases hq : polyValue q v <;> simp [swap b a hba]

def step : Word → Option Word
  | [] => none
  | [_] => none
  | (a,p) :: (b,q) :: w =>
    if b ≤ a then some (clean (replacement a b p q) ++ w)
    else (step ((b,q) :: w)).map ((a,p) :: ·)

theorem step_sound (u w : Word) (h : step u = some w) (v : Monomial) :
    value w v = value u v := by
  induction u using step.induct generalizing w with
  | case1 => simp [step] at h
  | case2 a => simp [step] at h
  | case3 a p b q l hba =>
    simp only [step, if_pos hba, Option.some.injEq] at h
    subst w
    simp only [value_append, value_clean, replacement_sound a b p q hba,
      value_cons, mul_assoc]
  | case4 a p b q l hba ih =>
    simp only [step, if_neg hba] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [value_cons, ih w hw]

def collect : Nat → Word → Word
  | 0, w => w
  | n+1, w => match step w with
    | none => w
    | some u => collect n u

theorem collect_sound (n : Nat) (w : Word) (v : Monomial) :
    value (collect n w) v = value w v := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [collect]
    split
    · rfl
    · rename_i u h
      exact (ih u).trans (step_sound w u h v)
/-- Ascending normal forms with Boolean coefficients. -/
def boolValue (b : Fin 21 → Bool) : Carrier :=
  (List.ofFn (fun i => if b i then generator i else 1)).prod

theorem boolValue_surjective : Function.Surjective boolValue := by
  intro x
  obtain ⟨n, rfl⟩ := normalForm_surjective x
  refine ⟨fun i => decide (n.val / 2 ^ i.val % 2 = 1), ?_⟩
  unfold boolValue normalForm
  rw [Theory.GroupTheory.BinaryCollection.product_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  have h := Nat.mod_two_eq_zero_or_one (n.val / 2 ^ i.val)
  rcases h with h | h <;> simp [h]

theorem boolValue_injective (hcard : Nat.card Carrier = 2 ^ 21) :
    Function.Injective boolValue := by
  apply (boolValue_surjective.bijective_of_nat_card_le ?_).injective
  simp [hcard, Nat.card_eq_fintype_card]

def coordinates (p : Fin 21 → Poly) : Word :=
  (List.finRange 21).map (fun i => (i, p i))

theorem value_coordinates (p : Fin 21 → Poly) (v : Monomial) :
    value (coordinates p) v = boolValue (fun i => polyValue (p i) v) := by
  simp only [value, coordinates, List.map_map, Function.comp_def, atomValue, boolValue, List.ofFn_eq_map]

theorem coordinates_injective (hcard : Nat.card Carrier = 2 ^ 21)
    (p q : Fin 21 → Poly) (v : Monomial)
    (h : value (coordinates p) v = value (coordinates q) v) :
    ∀ i, polyValue (p i) v = polyValue (q i) v := by
  rw [value_coordinates, value_coordinates] at h
  exact congrFun (boolValue_injective hcard h)

/-- Symbolic word with constant coefficient one on each letter. -/
def constant (w : List (Fin 21)) : Word := w.map (fun i => (i, [0]))

@[simp] theorem value_constant (w : List (Fin 21)) (v : Monomial) :
    value (constant w) v = wordValue w := by
  simp [constant, monomialValue, polyValue]

/-- Concrete application of the symbolic checker to a literal presentation word. -/
theorem word_eq_of_collect (n : Nat) (u w : List (Fin 21))
    (h : collect n (constant u) = constant w) : wordValue u = wordValue w := by
  have hs := collect_sound n (constant u) 0
  rw [h, value_constant, value_constant] at hs
  exact hs.symm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseCalculation.Symbolic
