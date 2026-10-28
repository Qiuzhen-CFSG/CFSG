module

public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# Interchanging the vertices of an amalgam

Reversal interchanges the two vertex maps and preserves compatible
isomorphisms. This records the vertex interchange allowed in the
Goldschmidt table, Aschbacher–Smith F.6.5, printed p.305.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

def reverse (α : RankTwoAmalgam L B R) : RankTwoAmalgam R B L :=
  ⟨α.right,α.left⟩

def Iso.reverse {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : Iso α β) : Iso α.reverse β.reverse where
  left := e.right
  middle := e.middle
  right := e.left
  left_commutes := e.right_commutes
  right_commutes := e.left_commutes
end Theory.GroupTheory.RankTwoAmalgam
