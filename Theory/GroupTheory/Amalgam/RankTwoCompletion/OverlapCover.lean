module

public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Tree

/-!
# Common coset coverings from the actual overlap

The pushout normal form gives the marked intersection in the universal
completion. Whenever a faithful completion has that same whole overlap, its
canonical pushout map is a coset covering. Comparing two such coverings
transfers rooted nonbacktracking path transitivity at every finite length.
No coprimality of endpoint indices or finiteness assumption is needed.

This applies to the equal-index ternary G₂ parabolics in Aschbacher–Smith
F.3.3–4 and F.4.6(1), printed pp.270–271 and 276.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam.Universal
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph.PathTransitivePolygon
universe u v w
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable {G : Type v} [Group G] {H : Type w} [Group H]
variable (α : RankTwoAmalgam L B R)
variable (c : FaithfulCompletion α (G := G))

/-- Whole overlap supplies the missing covering condition for the canonical lift. -/
theorem coverData_of_overlap
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    CoverData (cosetFamily α) c.cosetFamily (lift α c) where
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
    have hL : Function.Injective α.left := fun x y h =>
      c.middle_injective (congrArg c.left h)
    have hR : Function.Injective α.right := by
      intro x y h
      apply c.middle_injective
      exact (DFunLike.congr_fun c.compatible x).trans
        ((congrArg c.right h).trans (DFunLike.congr_fun c.compatible y).symm)
    change ((left α).range ⊓ (right α).range).map (lift α c) =
      c.left.range ⊓ c.right.range
    rw [overlap_eq α hL hR,hc]
    exact map_middle_range α c

/-- Transfer through the actual pushout, retaining either root and every length. -/
theorem rootPathTransitive_transfer_of_overlap
    (d : FaithfulCompletion α (G := H))
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range)
    (i : Bool) (n : ℕ)
    (ht : RootPathTransitive (graph c.cosetFamily) G (base c.cosetFamily i) n) :
    RootPathTransitive (graph d.cosetFamily) H (base d.cosetFamily i) n := by
  have h : RootPathTransitive (graph c.cosetFamily) G
      ((coverData_of_overlap α c hc).vertex (base (cosetFamily α) i)) n := by
    simpa only [CoverData.vertex_base] using ht
  simpa only [CoverData.vertex_base] using
    (coverData_of_overlap α c hc).transport_rootPathTransitive
      (coverData_of_overlap α d hd) n (base (cosetFamily α) i) h

/-- Rooted path transitivity agrees in any two completions with whole overlap. -/
theorem rootPathTransitive_iff_of_overlap
    (d : FaithfulCompletion α (G := H))
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range)
    (i : Bool) (n : ℕ) :
    RootPathTransitive (graph c.cosetFamily) G (base c.cosetFamily i) n ↔
      RootPathTransitive (graph d.cosetFamily) H (base d.cosetFamily i) n :=
  ⟨rootPathTransitive_transfer_of_overlap α c d hc hd i n,
    rootPathTransitive_transfer_of_overlap α d c hd hc i n⟩

end Theory.GroupTheory.RankTwoAmalgam.Universal
