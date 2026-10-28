module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.BinaryModel

/-!
# The two marked quotient reflections

An involution on the four-dimensional quotient fixing the first plane
pointwise has the form (v,w) ↦ (v+Pw,w). Its fixed space is exactly that
plane precisely when P is nonsingular. The second reflection is analogous.
Their center actions fix z and u respectively and exchange the other two
nonzero central vectors. The square map must intertwine these actual actions.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243;
the no-singular-transvection step supplies these exact fixed spaces.
-/

@[expose] public section
namespace Theory.GroupTheory.HyperbolicRecognition

abbrev Frame := Central × Central

def planeMap (P : Frame) (v : Central) : Central :=
  (v.1 * P.1.1 + v.2 * P.2.1, v.1 * P.1.2 + v.2 * P.2.2)

@[simp] theorem planeMap_zero (P : Frame) : planeMap P 0 = 0 := by
  ext <;> simp [planeMap]

theorem planeMap_add (P : Frame) (v w : Central) :
    planeMap P (v+w) = planeMap P v + planeMap P w := by
  ext <;> dsimp [planeMap] <;> ring

def Nonsingular (P : Frame) : Prop := ∀ v : Central, planeMap P v = 0 → v = 0
instance (P : Frame) : Decidable (Nonsingular P) := by unfold Nonsingular; infer_instance

def reflectA (P : Frame) (v : Vector) : Vector := (v.1 + planeMap P v.2, v.2)
def reflectB (P : Frame) (v : Vector) : Vector := (v.1, v.2 + planeMap P v.1)
def centerReflectA (c : Central) : Central := (c.1+c.2,c.2)
def centerReflectB (c : Central) : Central := (c.1,c.1+c.2)

def FirstReflection (M : Cross) (P : Frame) : Prop :=
  Nonsingular P ∧ ∀ v : Vector, quadratic M (reflectA P v) = centerReflectA (quadratic M v)
def SecondReflection (M : Cross) (P : Frame) : Prop :=
  Nonsingular P ∧ ∀ v : Vector, quadratic M (reflectB P v) = centerReflectB (quadratic M v)

instance (M : Cross) (P : Frame) : Decidable (FirstReflection M P) := by
  unfold FirstReflection; infer_instance
instance (M : Cross) (P : Frame) : Decidable (SecondReflection M P) := by
  unfold SecondReflection; infer_instance

def HasFirstReflection (M : Cross) : Prop := ∃ P : Frame, FirstReflection M P
def HasSecondReflection (M : Cross) : Prop := ∃ P : Frame, SecondReflection M P
instance (M : Cross) : Decidable (HasFirstReflection M) := by
  unfold HasFirstReflection; infer_instance
instance (M : Cross) : Decidable (HasSecondReflection M) := by
  unfold HasSecondReflection; infer_instance

def identityFrame : Frame := (cz,cu)
def exchangeFrame : Frame := (cu,cz)

end Theory.GroupTheory.HyperbolicRecognition
