module
public import Theory.GroupAction.CubicTree.Tracks

/-!
# Adjacent reflection data for a translation track

The two reflections fix consecutive vertices and reverse the integer
coordinate. A pair of involutions fixing adjacent vertices, each moving the
other vertex, constructs such a track by the existing alternating-line proof.
These literal action predicates are used to choose Goldschmidt's track with
reflections whenever possible, at the start of Section 6 (1980), p.395.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

def Track.HasReflections (t : Track Γ G) : Prop :=
  ∃ x y : G, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧
    (∀ i, x • t.vertex i = t.vertex (-i)) ∧
    (∀ i, y • t.vertex i = t.vertex (2-i))

def AdjacentInvolutionMovers (Γ : SimpleGraph V) (G : Type*) [Group G]
    [MulAction G V] : Prop :=
  ∃ (a b : V) (x y : G), Γ.Adj a b ∧
    x • a = a ∧ y • b = b ∧ x • b ≠ b ∧ y • a ≠ a ∧
    x ^ 2 = 1 ∧ y ^ 2 = 1

end Theory.GroupAction.CubicTree
