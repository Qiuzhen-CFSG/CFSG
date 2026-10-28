module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Universal
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
/-!
# Common pushout coverings of faithful rank-two completions

For finite endpoint groups whose order gcd is the marked middle order, the
canonical pushout lift has precisely the intersection required for a coset
covering. Its image and local injectivity statements therefore construct the
actual covering data for every faithful completion. Comparing the two covers
transfers rooted nonbacktracking path transitivity, with both types and every
finite length retained.

Source: Aschbacher--Smith, F.3.3--4 and F.4.6, printed pp.270 and 276--277.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
universe u v w
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable {G : Type v} [Group G] {H : Type w} [Group H]
variable (α : RankTwoAmalgam L B R)
namespace FaithfulCompletion
variable {α} (c : FaithfulCompletion α (G := G))
def cosetFamily : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range
end FaithfulCompletion
namespace Universal

def cosetFamily : Bool → Subgroup α.Universal :=
  fun i => bif i then (right α).range else (left α).range

variable [Finite L] [Finite R]
variable (hgcd : (Nat.card L).gcd (Nat.card R) = Nat.card B)
variable (c : FaithfulCompletion α (G := G))
include hgcd

theorem coverData : CoverData (cosetFamily α) c.cosetFamily (lift α c) where
  surjective := lift_surjective α c
  map_eq i := by
    cases i
    · exact map_left_range α c
    · exact map_right_range α c
  injective i := by
    cases i
    · exact injective_on_left α c
    · exact injective_on_right α c
  map_inf := by
    change ((left α).range ⊓ (right α).range).map (lift α c) = c.left.range ⊓ c.right.range
    have ho := (completion α c).overlap_eq_of_gcd hgcd
    change (left α).range ⊓ (right α).range = ((left α).comp α.left).range at ho
    rw [ho, c.overlap_eq_of_gcd hgcd]
    exact map_middle_range α c

/-- Canonical lifts preserve the original standard roots at both types. -/
@[simp] theorem coverData_vertex_base (i : Bool) :
    (coverData α hgcd c).vertex (base (cosetFamily α) i) = base c.cosetFamily i :=
  (coverData α hgcd c).vertex_base i

/-- Transfer rooted path transitivity through the actual common pushout.
The local marking is the original compatible identification of the amalgam. -/
theorem rootPathTransitive_transfer (d : FaithfulCompletion α (G := H))
    (i : Bool) (n : ℕ)
    (ht : RootPathTransitive (graph c.cosetFamily) G (base c.cosetFamily i) n) :
    RootPathTransitive (graph d.cosetFamily) H (base d.cosetFamily i) n := by
  have h : RootPathTransitive (graph c.cosetFamily) G
      ((coverData α hgcd c).vertex (base (cosetFamily α) i)) n := by
    exact (coverData_vertex_base α hgcd c i).symm ▸ ht
  exact (coverData_vertex_base α hgcd d i) ▸
    (coverData α hgcd c).transport_rootPathTransitive (coverData α hgcd d) n
      (base (cosetFamily α) i) h

/-- Path-transitivity is identical in all faithful completions at either
marked vertex, for every finite length. -/
theorem rootPathTransitive_iff (d : FaithfulCompletion α (G := H)) (i : Bool) (n : ℕ) :
    RootPathTransitive (graph c.cosetFamily) G (base c.cosetFamily i) n ↔
    RootPathTransitive (graph d.cosetFamily) H (base d.cosetFamily i) n :=
  ⟨rootPathTransitive_transfer α hgcd c d i n,
    rootPathTransitive_transfer α hgcd d c i n⟩
end Universal
end Theory.GroupTheory.RankTwoAmalgam
