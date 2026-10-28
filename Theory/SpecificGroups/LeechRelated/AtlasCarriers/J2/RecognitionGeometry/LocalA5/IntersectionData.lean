module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.VertexData

/-!
# The normalizer-of-X filter inside the local A₅

Rows normalizing the marked cubic are matched to their explicit S₃ words.
Every other row has a point disproving each possible nonidentity power image.
These candidate witnesses are checked by `Intersections`.
Source: Aschbacher, *Sporadic Groups*, 47.10, pp.266–267; retained ATLAS words.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.IntersectionData
open Theory.GroupTheory

def perm0 : Equiv.Perm (Fin 3) := tablePerm ![0, 1, 2] ![0, 1, 2] (by decide) (by decide)
def perm1 : Equiv.Perm (Fin 3) := tablePerm ![1, 2, 0] ![2, 0, 1] (by decide) (by decide)
def perm2 : Equiv.Perm (Fin 3) := tablePerm ![1, 0, 2] ![1, 0, 2] (by decide) (by decide)
def perm3 : Equiv.Perm (Fin 3) := tablePerm ![2, 0, 1] ![1, 2, 0] (by decide) (by decide)
def perm4 : Equiv.Perm (Fin 3) := tablePerm ![0, 2, 1] ![0, 2, 1] (by decide) (by decide)
def perm5 : Equiv.Perm (Fin 3) := tablePerm ![2, 1, 0] ![2, 1, 0] (by decide) (by decide)

def image (j : Fin 60) : Equiv.Perm (Fin 3) :=
  ![perm0, perm1, perm2, perm3, perm4, perm5] (⟨(85672898165824655870753189483839488 >>> (3*j.val)) % 8 % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6)

def badPoint (j : Fin 60) (k : Fin 2) : Fin 100 :=
  ⟨(0 >>> (7*(2*j.val+k.val))) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def xPower (j : Fin 2) (i : Fin 100) : Fin 100 :=
  if j.val = 0 then LocalIndexed.letterValue 0 i
  else LocalIndexed.letterValue 0 (LocalIndexed.letterValue 0 i)

def yPower (j : Fin 2) (i : Fin 100) : Fin 100 :=
  if j.val = 0 then LocalIndexed.letterValue 1 i
  else LocalIndexed.letterValue 1 (LocalIndexed.letterValue 1 i)

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.IntersectionData
