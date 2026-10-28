module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.Systems
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.Data.Set.Card

/-!
# Exact join types and suborbit inputs for the J₂ graph

The two nonedge relations use actual equivalences to SL₂(3) and A₅.
Together with equality and the A₄ edge relation, they are the four cases
of Aschbacher, *Sporadic Groups* (1994), 47.5, p.263.

`FourSuborbits` is an explicit conditional interface for that source
calculation. Its labels are determined by these actual joins, and its
transitivity uses the literal normalizer and the existing conjugation action.
This module does not construct the source suborbits from `Seed`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

/-- The concrete matrix group appearing in the length-135 suborbit. -/
abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

def sl2Join (D : Seed G) (A B : D.Vertex) : Prop :=
  Nonempty (↥(A.val ⊔ B.val) ≃* SL23)

def a5Join (D : Seed G) (A B : D.Vertex) : Prop :=
  Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 5))

/-- The source alternatives on every ordered pair of vertices. -/
def FourJoinTypes (D : Seed G) : Prop :=
  ∀ A B : D.Vertex, A = B ∨ D.graph.Adj A B ∨ sl2Join D A B ∨ a5Join D A B

theorem card_join_of_adj (D : Seed G) {A B : D.Vertex} (h : D.graph.Adj A B) :
    Nat.card (A.val ⊔ B.val : Subgroup G) = 12 := by
  rw [Nat.card_congr h.2.some.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem card_join_of_sl2Join (D : Seed G) {A B : D.Vertex} (h : sl2Join D A B) :
    Nat.card (A.val ⊔ B.val : Subgroup G) = 24 := by
  rw [Nat.card_congr h.some.toEquiv, Atlas.card_sl_two]
  norm_num

theorem card_join_of_a5Join (D : Seed G) {A B : D.Vertex} (h : a5Join D A B) :
    Nat.card (A.val ⊔ B.val : Subgroup G) = 60 := by
  rw [Nat.card_congr h.some.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- Labels are fixed by equality and actual join isomorphisms, not arbitrary tags. -/
noncomputable def orbitLabel (D : Seed G) (V : D.Vertex) : Fin 4 := by
  classical
  exact if V = D.base then 0 else if D.graph.Adj D.base V then 1
    else if sl2Join D D.base V then 2 else 3

@[simp] theorem orbitLabel_base (D : Seed G) : orbitLabel D D.base = 0 := by
  classical
  simp [orbitLabel]

theorem orbitLabel_of_adj (D : Seed G) {V : D.Vertex} (h : D.graph.Adj D.base V) :
    orbitLabel D V = 1 := by
  classical
  simp [orbitLabel, h, h.ne.symm]

/-- The label 1 is exactly the graph edge relation. -/
theorem orbitLabel_eq_one_iff (D : Seed G) (V : D.Vertex) :
    orbitLabel D V = 1 ↔ D.graph.Adj D.base V := by
  classical
  unfold orbitLabel
  split_ifs <;> simp_all

def subdegrees (i : Fin 4) : ℕ := ![1, 36, 135, 108] i

/-- Remaining source calculations; their producer must prove every field from `Seed`. -/
structure FourSuborbits (D : Seed G) : Prop where
  joins : FourJoinTypes D
  transitive : ∀ U V : D.Vertex, orbitLabel D U = orbitLabel D V →
    ∃ k : normalizer (D.X : Set G), (k : G) • U = V
  card : ∀ i : Fin 4, Nat.card {V : D.Vertex // orbitLabel D V = i} = subdegrees i

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
