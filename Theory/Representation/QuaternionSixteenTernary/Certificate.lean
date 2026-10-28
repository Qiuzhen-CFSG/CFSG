module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# A small cubic-extension certificate for the ternary quaternion frame

The standard four-dimensional quaternion-sixteen frame has a normal Q₈.
A cubic normalizing Q₈ and inverted by the marked reflection is determined
by the images of two Q₈ generators and one vector. The cubic/reflection
relations leave five possible generator images (including the identity
image); checking their 81 possible vectors leaves exactly four matrices.
All finite assertions here are checked by the Lean kernel.

Source application: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

@[expose] public section
namespace Theory.Representation.QuaternionSixteenTernary
abbrev V := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3
instance : DecidableEq V := inferInstanceAs (DecidableEq (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3))
abbrev Mat := V × V × V × V
instance : DecidableEq Mat := inferInstanceAs (DecidableEq (V × V × V × V))

def e : Fin 4 → V := ![(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
def a (v : V) : V := (v.2.1,v.1+v.2.1,v.2.2.2,v.2.2.1-v.2.2.2)
def r (v : V) : V := (-v.2.2.1+v.2.2.2,-v.2.2.2,v.1+v.2.1,v.2.1)
def qi (v : V) : V := a (a v)
def qj (v : V) : V := a (r v)
def q (i : Fin 8) (v : V) : V := match i.val with
  | 0 => v
  | 1 => -v
  | 2 => qi v
  | 3 => -(qi v)
  | 4 => qj v
  | 5 => -(qj v)
  | 6 => qi (qj v)
  | _ => -(qi (qj v))
def lin (m : Mat) (v : V) : V :=
  (v.1*m.1.1 + v.2.1*m.2.1.1 + v.2.2.1*m.2.2.1.1 + v.2.2.2*m.2.2.2.1,
   v.1*m.1.2.1 + v.2.1*m.2.1.2.1 + v.2.2.1*m.2.2.1.2.1 + v.2.2.2*m.2.2.2.2.1,
   v.1*m.1.2.2.1 + v.2.1*m.2.1.2.2.1 + v.2.2.1*m.2.2.1.2.2.1 + v.2.2.2*m.2.2.2.2.2.1,
   v.1*m.1.2.2.2 + v.2.1*m.2.1.2.2.2 + v.2.2.1*m.2.2.1.2.2.2 + v.2.2.2*m.2.2.2.2.2.2)
def candidate (i j : Fin 8) (v : V) : Mat :=
  (v,q i v-v,-q i (q j v)-q j v,q j v)
def good (i j : Fin 8) (m : Mat) : Prop :=
  (∀ t : Fin 4, lin m (qi (e t)) = q i (lin m (e t))) ∧
  (∀ t : Fin 4, lin m (qj (e t)) = q j (lin m (e t))) ∧
  (∀ t : Fin 4, lin m (lin m (lin m (e t))) = e t) ∧
  (∀ t : Fin 4, r (lin m (e t)) = lin m (lin m (r (e t)))) ∧
  (∃ t : Fin 4, lin m (e t) ≠ e t)
instance (i j : Fin 8) (m : Mat) : Decidable (good i j m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
def y0 : Mat := ((0,2,1,0),(2,2,1,1),(1,0,0,1),(2,1,1,2))
def y1 : Mat := ((0,2,2,0),(2,2,2,2),(2,0,0,1),(1,2,1,2))
def y2 : Mat := ((2,1,1,0),(1,0,1,1),(1,0,2,2),(2,1,2,0))
def y3 : Mat := ((2,1,2,0),(1,0,2,2),(2,0,2,2),(1,2,2,0))
def listed (m : Mat) : Prop := m=y0 ∨ m=y1 ∨ m=y2 ∨ m=y3
instance (m : Mat) : Decidable (listed m) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def possibleImages (i j : Fin 8) : Prop :=
  (i=2 ∧ j=4) ∨ (i=6 ∧ j=2) ∨ (i=7 ∧ j=3) ∨ (i=5 ∧ j=6) ∨ (i=4 ∧ j=6)
instance (i j : Fin 8) : Decidable (possibleImages i j) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

def negativeCode (i : Fin 8) : Fin 8 := ![1,0,3,2,5,4,7,6] i
def reflectionCode (i : Fin 8) : Fin 8 := ![0,1,3,2,7,6,5,4] i
def codeMul (i j : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7],![1,0,3,2,5,4,7,6],![2,3,1,0,6,7,5,4],![3,2,0,1,7,6,4,5],
    ![4,5,7,6,1,0,2,3],![5,4,6,7,0,1,3,2],![6,7,4,5,3,2,1,0],![7,6,5,4,2,3,0,1]] i j
def imageCode (i j k : Fin 8) : Fin 8 :=
  ![0,1,i,negativeCode i,j,negativeCode j,codeMul i j,negativeCode (codeMul i j)] k

theorem possibleImages_of_relations : ∀ i j : Fin 8,
    (∀ k, imageCode i j (imageCode i j (imageCode i j k))=k) →
    (∀ k, reflectionCode (imageCode i j k)=imageCode i j (imageCode i j (reflectionCode k))) →
    possibleImages i j := by decide +kernel

theorem q_faithful : ∀ i j : Fin 8, q i (e 0)=q j (e 0) → i=j := by decide +kernel

theorem q_negative : ∀ (i : Fin 8) (v : V), q (negativeCode i) v = -q i v := by decide +kernel

theorem q_mul : ∀ (i j : Fin 8) (v : V), q (codeMul i j) v = q i (q j v) := by decide +kernel

theorem q_reflection : ∀ (i : Fin 8) (v : V), r (q i v)=q (reflectionCode i) (r v) := by decide +kernel

theorem cubic_candidates : ∀ (i j : Fin 8), possibleImages i j → ∀ v : V,
    good i j (candidate i j v) → listed (candidate i j v) := by
  decide +kernel
end Theory.Representation.QuaternionSixteenTernary
