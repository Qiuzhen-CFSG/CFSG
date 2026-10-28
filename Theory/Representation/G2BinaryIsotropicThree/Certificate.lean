module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Fifteen isotropic three-spaces through a fixed binary vector

After fixing the first vector, a totally isotropic three-space projects to an
isotropic plane in the four middle coordinates. There are fifteen such planes.
The short word table carries seven to the distinguished three-space using
only derived-group generators, and eight to a three-space with trivial
pointwise stabilizer. All certificates use ordinary kernel reduction on at
most two four-bit vectors; no group-order census is assumed.

Source: Aschbacher–Smith 13.3.12(3), printed p.890. The actual octonion-word
interpretation is proved in the model extension importing this certificate.
-/

@[expose] public section

namespace Atlas.G2.Natural.BinaryIsotropicThree.Certificate
abbrev Four := Fin 4 → ZMod 2
def pairing (x y : Four) : ZMod 2 := x 0*y 3+x 3*y 0+x 1*y 2+x 2*y 1
def inPair (x y z : Four) : Prop := z=0 ∨ z=x ∨ z=y ∨ z=x+y
instance (x y z : Four) : Decidable (inPair x y z) := inferInstanceAs (Decidable (_∨_∨_∨_))
def left : Fin 15 → Four := ![
    ![1,0,0,0],
    ![1,0,0,0],
    ![1,0,0,0],
    ![0,1,0,0],
    ![0,1,0,0],
    ![1,1,0,0],
    ![1,1,0,0],
    ![0,0,1,0],
    ![0,0,1,0],
    ![1,0,1,0],
    ![1,0,1,0],
    ![0,1,1,0],
    ![0,1,1,0],
    ![1,1,1,0],
    ![1,1,1,0]]
def right : Fin 15 → Four := ![
    ![0,1,0,0],
    ![0,0,1,0],
    ![0,1,1,0],
    ![0,0,0,1],
    ![1,0,0,1],
    ![0,0,1,1],
    ![1,0,1,1],
    ![0,0,0,1],
    ![1,0,0,1],
    ![0,1,0,1],
    ![1,1,0,1],
    ![0,0,0,1],
    ![1,0,0,1],
    ![0,1,0,1],
    ![1,1,0,1]]
def words : Fin 15 → List (Fin 5) := ![
    [],
    [4,0,1,0,4],
    [4,3,1,3,4],
    [1,3,4,3],
    [1,3,4],
    [4,3,4,3,1],
    [4,3,1,0,4],
    [],
    [2],
    [3,2],
    [3],
    [2,4],
    [2,4,2],
    [2,4,3,2],
    [2,4,3]]
def other : Fin 15 → Bool := ![false,false,false,false,false,false,false,true,true,true,true,true,true,true,true]

abbrev Six := Fin 6 → ZMod 2
def embed (v : Four) : Six := ![0,v 0,v 1,v 2,v 3,0]
def first : Six := ![1,0,0,0,0,0]
def stepA (v : Six) : Six := ![v 0+v 2+v 5,v 1+v 3+v 4+v 5,v 2+v 4,v 3+v 5,v 4,v 5]
def stepB (v : Six) : Six := ![v 3,v 5,v 1,v 4,v 0,v 2]
def stepD (v : Six) : Six := ![v 0+v 2,v 1+v 4,v 2,v 3+v 5,v 4,v 5]
def step : Fin 5 → Six → Six := ![stepA,stepB,stepD,fun v=>stepA (stepA (stepA v)),fun v=>stepB (stepB v)]
def wordAction : List (Fin 5) → Six → Six
 | [],v=>v
 | i::w,v=>step i (wordAction w v)
def inTarget (b : Bool) (v : Six) : Prop :=
 if b then v 1=0 ∧ v 2=0 ∧ v 5=0 else v 3=0 ∧ v 4=0 ∧ v 5=0
instance (b : Bool) (v : Six) : Decidable (inTarget b v) :=
 inferInstanceAs (Decidable (if b then _ else _))

theorem image_certificate : ∀i,
    inTarget (other i) (wordAction (words i) first) ∧
    inTarget (other i) (wordAction (words i) (embed (left i))) ∧
    inTarget (other i) (wordAction (words i) (embed (right i))) := by decide +kernel
theorem derived_words : ∀i,other i=false→∀j∈words i,j≠2 := by decide +kernel

theorem basis_independent : ∀i, left i≠0 ∧ right i≠0 ∧ left i≠right i := by decide +kernel
def admissible (x y : Four) : Prop := x≠0 ∧ y≠0 ∧ x≠y ∧ pairing x y=0
instance (x y : Four) : Decidable (admissible x y) :=
 inferInstanceAs (Decidable (_∧_∧_∧_))
def covered (x y : Four) : Prop := ∃i,inPair (left i) (right i) x ∧ inPair (left i) (right i) y
instance (x y : Four) : Decidable (covered x y) :=
 inferInstanceAs (Decidable (∃i:Fin 15,inPair (left i) (right i) x ∧ inPair (left i) (right i) y))
theorem coverage : ∀x y : Four,admissible x y→covered x y := by decide +kernel

end Atlas.G2.Natural.BinaryIsotropicThree.Certificate
