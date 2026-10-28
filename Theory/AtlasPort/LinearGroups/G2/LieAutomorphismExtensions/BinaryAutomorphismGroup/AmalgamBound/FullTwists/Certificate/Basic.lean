module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.Data
public import Mathlib.Tactic.FinCases

/-!
# Word induction and composition for finite endpoint certificates

Multiplication-preserving maps respect positive words. Endpoint permutations
with literal overlap squares compose, so a small checked generating set
constructs all extensions used by the full binary G₂ certificate. No group
realization or associativity of an arbitrary finite table is assumed here.

Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
The imported data retain the ATLAS attribution and license.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate

/-- Positive words, evaluated with the identity row as the empty word. -/
def eval {n : ℕ} (mul : Fin n → Fin n → Fin n) (zero : Fin n)
    (gs : Fin 3 → Fin n) : List (Fin 3) → Fin n
  | [] => zero
  | a :: w => mul (gs a) (eval mul zero gs w)

theorem map_eval {n : ℕ} (mul : Fin n → Fin n → Fin n) (zero : Fin n)
    (f : Fin n → Fin n) (hzero : f zero = zero)
    (hmul : ∀ i j, f (mul i j) = mul (f i) (f j))
    (gs : Fin 3 → Fin n) (w : List (Fin 3)) :
    f (eval mul zero gs w) = eval mul zero (fun a => f (gs a)) w := by
  induction w with
  | nil => exact hzero
  | cons a w ih => simp only [eval, hmul, ih]

def generators : Fin 3 → Fin 64 := ![1, 2, 3]
def images (k : Fin 256) : Fin 3 → Fin 64 :=
  ![firstImage k, secondImage k, thirdImage k]

def relations : List (List (Fin 3)) :=
  [[1, 1], [2, 2], [1, 2, 1, 2], [0, 0, 1, 0, 0, 1],
    [0, 1, 2, 0, 1, 2], [0, 2, 0, 2, 0, 2, 0, 2]]

def Candidate (x y z : Fin 64) : Prop :=
  eval middleMul 0 ![x, y, z] [0, 0, 0, 0] ≠ 0 ∧
    y ≠ 0 ∧ z ≠ 0 ∧ ∀ w ∈ relations, eval middleMul 0 ![x, y, z] w = 0

instance (x y z : Fin 64) : Decidable (Candidate x y z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ w ∈ relations, _))

/-- An endpoint automorphism with its exact overlap restriction. -/
structure Extension (mul : Fin 192 → Fin 192 → Fin 192)
    (overlap : Fin 64 → Fin 192) where
  endpoint : Equiv.Perm (Fin 192)
  middle : Equiv.Perm (Fin 64)
  map_mul : ∀ i j, endpoint (mul i j) = mul (endpoint i) (endpoint j)
  square : ∀ i, endpoint (overlap i) = overlap (middle i)

def Extension.refl (mul : Fin 192 → Fin 192 → Fin 192)
    (overlap : Fin 64 → Fin 192) : Extension mul overlap where
  endpoint := Equiv.refl _
  middle := Equiv.refl _
  map_mul _ _ := rfl
  square _ := rfl

def Extension.comp {mul : Fin 192 → Fin 192 → Fin 192}
    {overlap : Fin 64 → Fin 192} (a b : Extension mul overlap) :
    Extension mul overlap where
  endpoint := b.endpoint.trans a.endpoint
  middle := b.middle.trans a.middle
  map_mul i j := by
    change a.endpoint (b.endpoint (mul i j)) =
      mul (a.endpoint (b.endpoint i)) (a.endpoint (b.endpoint j))
    rw [b.map_mul, a.map_mul]
  square i := by
    change a.endpoint (b.endpoint (overlap i)) = overlap (a.middle (b.middle i))
    rw [b.square, a.square]

def actWord {α : Type*} (gs : Fin 5 → α → α) : List (Fin 5) → α → α
  | [], i => i
  | a :: w, i => gs a (actWord gs w i)

def Extension.word {mul : Fin 192 → Fin 192 → Fin 192}
    {overlap : Fin 64 → Fin 192} (gs : Fin 5 → Extension mul overlap) :
    List (Fin 5) → Extension mul overlap
  | [] => Extension.refl mul overlap
  | a :: w => (gs a).comp (Extension.word gs w)

theorem Extension.word_middle {mul : Fin 192 → Fin 192 → Fin 192}
    {overlap : Fin 64 → Fin 192} (gs : Fin 5 → Extension mul overlap)
    (w : List (Fin 5)) (i : Fin 64) :
    (Extension.word gs w).middle i = actWord (fun a => (gs a).middle) w i := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (gs a).middle ih

def leftFactor (k : Fin 256) : Fin 64 → Fin 64 := actWord middleSeed (factorWord k)
def rightFactor (k : Fin 256) (i : Fin 64) : Fin 64 :=
  if factorRight k then rightMiddleSeed i else i

/-- Small blocks keep the kernel's temporary reduction cache bounded. -/
def row (b : Fin 12) (i : Fin 16) : Fin 192 :=
  ⟨16*b.val + i.val, by omega⟩

theorem row_split (i : Fin 192) : row (@Fin.divNat 12 16 i) (@Fin.modNat 12 16 i) = i := by
  apply Fin.ext
  simp only [row, Fin.divNat, Fin.modNat]
  omega

theorem forall_rows (P : Fin 192 → Prop)
    (h : ∀ b : Fin 12, ∀ i : Fin 16, P (row b i)) : ∀ i, P i := by
  intro i
  rw [← row_split i]
  exact h _ _

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate
