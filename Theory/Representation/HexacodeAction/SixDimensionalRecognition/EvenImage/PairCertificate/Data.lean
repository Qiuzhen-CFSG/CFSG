module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation

/-!
# Finite arithmetic for the normalized hexacode pair

A four-constructor type encodes F₄ and nine entries encode a three by three
matrix. The candidate table lists conjugates of the four model words under
sixteen explicitly invertible matrices commuting with the fixed first matrix.
The tables are data only: the coverage and witness identities are checked by
Lean's kernel in the following modules, and interpreted on the actual code
carrier by `PairCertificate`.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464), and the diagnostic
`EvenImage/source/PairCheck.g`. No classification or class-coverage assertion
from that diagnostic is used.
-/

@[expose] public section
namespace Representation.Hexacode.SixDimensional.EvenImage.PairData
inductive Q where
  | z | o | w | t
  deriving DecidableEq
instance : Fintype Q := ⟨{Q.z,Q.o,Q.w,Q.t}, by intro x; cases x <;> simp⟩
open Q

def add : Q → Q → Q
  | z, z => z
  | z, o => o
  | z, w => w
  | z, t => t
  | o, z => o
  | o, o => z
  | o, w => t
  | o, t => w
  | w, z => w
  | w, o => t
  | w, w => z
  | w, t => o
  | t, z => t
  | t, o => w
  | t, w => o
  | t, t => z

def mul : Q → Q → Q
  | z, z => z
  | z, o => z
  | z, w => z
  | z, t => z
  | o, z => z
  | o, o => o
  | o, w => w
  | o, t => t
  | w, z => z
  | w, o => w
  | w, w => t
  | w, t => o
  | t, z => z
  | t, o => t
  | t, w => o
  | t, t => w

structure M where
  a : Q
  b : Q
  c : Q
  d : Q
  e : Q
  f : Q
  g : Q
  h : Q
  i : Q
  deriving DecidableEq

def mm (a b : M) : M :=
  ⟨add (add (mul a.a b.a) (mul a.b b.d)) (mul a.c b.g),
   add (add (mul a.a b.b) (mul a.b b.e)) (mul a.c b.h),
   add (add (mul a.a b.c) (mul a.b b.f)) (mul a.c b.i),
   add (add (mul a.d b.a) (mul a.e b.d)) (mul a.f b.g),
   add (add (mul a.d b.b) (mul a.e b.e)) (mul a.f b.h),
   add (add (mul a.d b.c) (mul a.e b.f)) (mul a.f b.i),
   add (add (mul a.g b.a) (mul a.h b.d)) (mul a.i b.g),
   add (add (mul a.g b.b) (mul a.h b.e)) (mul a.i b.h),
   add (add (mul a.g b.c) (mul a.h b.f)) (mul a.i b.i)⟩

def ident : M := ⟨o,z,z,z,o,z,z,z,o⟩
def first : M := ⟨o,o,o,o,z,z,z,o,z⟩
def second : M := ⟨z,z,o,w,z,z,z,t,z⟩
def cube (m : M) := mm (mm m m) m
def fifth (m : M) := let s := mm m m; mm (mm s s) m

def candidates : Fin 64 → M := ![
  ⟨z,z,o,w,z,z,z,t,z⟩,
  ⟨t,t,t,w,t,o,o,z,z⟩,
  ⟨t,o,z,z,o,z,z,w,w⟩,
  ⟨z,w,w,z,w,o,o,o,w⟩,
  ⟨w,w,w,t,z,z,o,t,w⟩,
  ⟨o,t,w,o,o,o,z,w,z⟩,
  ⟨o,z,z,w,w,z,o,o,t⟩,
  ⟨w,o,z,z,t,o,z,z,o⟩,
  ⟨w,z,z,w,o,o,t,z,t⟩,
  ⟨t,z,t,t,o,w,z,z,w⟩,
  ⟨w,z,t,w,o,w,z,z,t⟩,
  ⟨t,z,z,t,o,o,t,z,w⟩,
  ⟨t,z,w,z,t,z,o,w,z⟩,
  ⟨w,w,t,t,o,t,w,z,t⟩,
  ⟨t,t,w,t,z,t,w,o,t⟩,
  ⟨w,o,t,z,w,z,o,t,z⟩,
  ⟨z,z,o,t,z,z,z,w,z⟩,
  ⟨w,w,w,t,w,o,o,z,z⟩,
  ⟨z,t,t,z,t,o,o,o,t⟩,
  ⟨w,o,z,z,o,z,z,t,t⟩,
  ⟨t,t,t,w,z,z,o,w,t⟩,
  ⟨o,w,t,o,o,o,z,t,z⟩,
  ⟨t,o,z,z,w,o,z,z,o⟩,
  ⟨o,z,z,t,t,z,o,o,w⟩,
  ⟨w,z,t,z,w,z,o,t,z⟩,
  ⟨t,t,w,w,o,w,t,z,w⟩,
  ⟨t,o,w,z,t,z,o,w,z⟩,
  ⟨w,w,t,w,z,w,t,o,w⟩,
  ⟨t,z,z,t,o,o,w,z,w⟩,
  ⟨w,z,w,w,o,t,z,z,t⟩,
  ⟨w,z,z,w,o,o,w,z,t⟩,
  ⟨t,z,w,t,o,t,z,z,w⟩,
  ⟨z,o,z,w,t,o,z,z,t⟩,
  ⟨t,z,z,z,w,z,o,o,o⟩,
  ⟨t,t,w,t,o,o,z,w,w⟩,
  ⟨z,w,w,o,z,z,o,t,z⟩,
  ⟨o,t,w,z,t,z,z,z,w⟩,
  ⟨w,z,z,z,z,o,o,t,w⟩,
  ⟨w,w,t,w,w,z,z,o,z⟩,
  ⟨o,o,o,w,o,o,o,w,z⟩,
  ⟨w,o,w,z,w,o,z,t,z⟩,
  ⟨t,t,t,t,z,w,t,o,t⟩,
  ⟨w,w,w,t,o,w,t,z,t⟩,
  ⟨t,z,t,z,t,o,z,w,z⟩,
  ⟨w,o,t,t,z,t,o,o,w⟩,
  ⟨t,o,z,w,z,z,w,o,t⟩,
  ⟨w,o,z,t,z,z,w,o,w⟩,
  ⟨t,o,t,w,z,t,o,o,t⟩,
  ⟨z,o,z,t,w,o,z,z,w⟩,
  ⟨w,z,z,z,t,z,o,o,o⟩,
  ⟨z,t,t,o,z,z,o,w,z⟩,
  ⟨w,w,t,w,o,o,z,t,t⟩,
  ⟨o,w,t,z,w,z,z,z,t⟩,
  ⟨t,z,z,z,z,o,o,w,t⟩,
  ⟨o,o,o,t,o,o,o,t,z⟩,
  ⟨t,t,w,t,t,z,z,o,z⟩,
  ⟨t,o,w,w,z,w,o,o,t⟩,
  ⟨w,o,z,t,z,z,t,o,w⟩,
  ⟨w,o,w,t,z,w,o,o,w⟩,
  ⟨t,o,z,w,z,z,t,o,t⟩,
  ⟨t,o,t,z,t,o,z,w,z⟩,
  ⟨w,w,w,w,z,t,w,o,w⟩,
  ⟨w,z,w,z,w,o,z,t,z⟩,
  ⟨t,t,t,w,o,t,w,z,w⟩]


def conjugator : Fin 16 → M := ![
  ⟨o,z,z,z,o,z,z,z,o⟩,
  ⟨z,z,o,o,o,o,o,z,z⟩,
  ⟨t,z,w,w,o,w,w,z,t⟩,
  ⟨w,z,t,t,o,t,t,z,w⟩,
  ⟨o,o,o,o,z,z,z,o,z⟩,
  ⟨z,o,z,z,z,o,o,o,o⟩,
  ⟨t,o,t,t,z,w,w,o,w⟩,
  ⟨w,o,w,w,z,t,t,o,t⟩,
  ⟨o,w,w,w,t,z,z,w,t⟩,
  ⟨z,w,t,t,t,o,o,w,w⟩,
  ⟨t,w,z,z,t,w,w,w,o⟩,
  ⟨w,w,o,o,t,t,t,w,z⟩,
  ⟨o,t,t,t,w,z,z,t,w⟩,
  ⟨z,t,w,w,w,o,o,t,t⟩,
  ⟨t,t,o,o,w,w,w,t,z⟩,
  ⟨w,t,z,z,w,t,t,t,o⟩]

def conjugatorInv : Fin 16 → M := ![
  ⟨o,z,z,z,o,z,z,z,o⟩,
  ⟨z,z,o,o,o,o,o,z,z⟩,
  ⟨t,z,w,w,o,w,w,z,t⟩,
  ⟨w,z,t,t,o,t,t,z,w⟩,
  ⟨z,o,z,z,z,o,o,o,o⟩,
  ⟨o,o,o,o,z,z,z,o,z⟩,
  ⟨w,o,w,w,z,t,t,o,t⟩,
  ⟨t,o,t,t,z,w,w,o,w⟩,
  ⟨w,w,o,o,t,t,t,w,z⟩,
  ⟨t,w,z,z,t,w,w,w,o⟩,
  ⟨z,w,t,t,t,o,o,w,w⟩,
  ⟨o,w,w,w,t,z,z,w,t⟩,
  ⟨t,t,o,o,w,w,w,t,z⟩,
  ⟨w,t,z,z,w,t,t,t,o⟩,
  ⟨o,t,t,t,w,z,z,t,w⟩,
  ⟨z,t,w,w,w,o,o,t,t⟩]

def words : Fin 4 → List (Fin 4) := ![
  [1],
  [2,1,0,0,3,0,0,1,2],
  [0,0,3,2],
  [2,3,2,2,1,2,2,3]]

def letter : Fin 4 → M := ![first, second, cube first, mm second second]
def word (w : List (Fin 4)) : M := (w.map letter).foldr mm ident

def witness (k : Fin 64) : Fin 16 := ⟨k.val % 16, Nat.mod_lt _ (by decide)⟩
def representative (k : Fin 64) : Fin 4 := ⟨k.val / 16, Nat.div_lt_of_lt_mul k.isLt⟩

def Relations (v : M) : Prop :=
  cube v = ident ∧ fifth (mm first v) = ident ∧ cube (mm first (mm v v)) = ident
instance (v : M) : Decidable (Relations v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Representation.Hexacode.SixDimensional.EvenImage.PairData
