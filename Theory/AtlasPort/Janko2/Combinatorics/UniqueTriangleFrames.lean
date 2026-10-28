/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/UniqueTriangleFrames.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

/-!
# UniqueTriangleFrames

A symmetric irreflexive relation with unique common neighbors determines a
unique triangle through each adjacent pair. This yields an equivalence between
ordered edges and triangle-edge incidences.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/UniqueTriangleFrames.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev RelationTriangle {X : Type*} (R : X → X → Prop) :=
  {F : Finset X // F.card=3 ∧ (↑F : Set X).Pairwise R}

def relationTriangleOfTriple {X : Type*} (R : X → X → Prop)
    (hsym : ∀ ⦃x y : X⦄, R x y → R y x) (hirr : ∀ x : X, ¬ R x x) (x y z : X)
    (hxy : R x y) (hxz : R x z) (hyz : R y z) : RelationTriangle R := by
  classical
  have hne : x≠y := by rintro rfl; exact hirr x hxy
  have hnz : x≠z := by rintro rfl; exact hirr x hxz
  have hyz0 : y≠z := by rintro rfl; exact hirr y hyz
  refine ⟨{x,y,z},by simp [hne,hnz,hyz0],?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first | exact (hab rfl).elim | exact hxy | exact hxz | exact hyz |
    exact hsym hxy | exact hsym hxz | exact hsym hyz

/-- A symmetric irreflexive relation with unique common neighbors gives a
unique unordered triangle through every ordered adjacent pair. -/
theorem unique_triangle_through_pair_of_completion {X : Type*} (R : X → X → Prop)
    (hsym : ∀ ⦃x y : X⦄, R x y → R y x) (hirr : ∀ x : X, ¬ R x x)
    (x y : X) (hxy : R x y) (hu : ∃! z,R x z ∧ R y z) :
    ∃! F : RelationTriangle R,x∈F.val ∧ y∈F.val := by
  classical
  have hne : x≠y := by rintro rfl; exact hirr x hxy
  obtain ⟨z,hz,hzu⟩ := hu
  have hxz : x≠z := by rintro rfl; exact hirr x hz.1
  have hyz : y≠z := by rintro rfl; exact hirr y hz.2
  let B : Finset X := {x,y,z}
  have hB : B.card=3 := by simp [B,hne,hxz,hyz]
  have hp : (↑B : Set X).Pairwise R := by
    intro a ha b hb hab
    simp only [B,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact (hab rfl).elim | exact hxy | exact hz.1 | exact hz.2 |
      exact hsym hxy | exact hsym hz.1 | exact hsym hz.2
  refine ⟨⟨B,hB,hp⟩,⟨by simp [B],by simp [B]⟩,?_⟩
  intro F hF
  obtain ⟨w,hw,hwxy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x,y} : Finset X).card<F.val.card by rw [F.property.1]; simp [hne])
  have hwx : w≠x := by intro he; apply hwxy; simp [he]
  have hwy : w≠y := by intro he; apply hwxy; simp [he]
  have hwz : w=z := hzu w ⟨F.property.2 hF.1 hw hwx.symm,F.property.2 hF.2 hw hwy.symm⟩
  have hsub : B⊆F.val := by
    intro a ha
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hF.1
    · exact hF.2
    · exact hwz ▸ hw
  apply Subtype.ext
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hB,F.property.1])).symm

theorem unique_triangle_through_pair {X : Type*} (R : X → X → Prop)
    (hsym : ∀ ⦃x y : X⦄, R x y → R y x) (hirr : ∀ x : X, ¬ R x x)
    (hu : ∀ x y,R x y → ∃! z,R x z ∧ R y z)
    (x y : X) (hxy : R x y) :
    ∃! F : RelationTriangle R,x∈F.val ∧ y∈F.val :=
  unique_triangle_through_pair_of_completion R hsym hirr x y hxy (hu x y hxy)

abbrev RelationEdge {X : Type*} (R : X → X → Prop) := {p : X × X // R p.1 p.2}
abbrev TriangleEdgeIncidence {X : Type*} (R : X → X → Prop) :=
  (F : RelationTriangle R) × {p : X × X // p∈F.val.offDiag}

def triangleEdgeMap {X : Type*} (R : X → X → Prop) :
    TriangleEdgeIncidence R → RelationEdge R := fun p =>
  ⟨p.2.val,p.1.property.2 (Finset.mem_offDiag.mp p.2.property).1
    (Finset.mem_offDiag.mp p.2.property).2.1 (Finset.mem_offDiag.mp p.2.property).2.2⟩

def triangleEdgeEquiv {X : Type*} (R : X → X → Prop)
    (hsym : ∀ ⦃x y : X⦄, R x y → R y x) (hirr : ∀ x : X, ¬ R x x)
    (hu : ∀ x y,R x y → ∃! z,R x z ∧ R y z) :
    TriangleEdgeIncidence R ≃ RelationEdge R := by
  classical
  apply Equiv.ofBijective (triangleEdgeMap R)
  constructor
  · rintro ⟨F,p⟩ ⟨G,q⟩ h
    have hpq : p.val=q.val := congrArg Subtype.val h
    have hF := Finset.mem_offDiag.mp p.property
    have hG := Finset.mem_offDiag.mp q.property
    obtain ⟨B,hB,huB⟩ := unique_triangle_through_pair R hsym hirr hu p.val.1 p.val.2
      (F.property.2 hF.1 hF.2.1 hF.2.2)
    have he : F=G := (huB F ⟨hF.1,hF.2.1⟩).trans
      (huB G (by simpa only [hpq] using And.intro hG.1 hG.2.1)).symm
    subst G
    exact congrArg (Sigma.mk F) (Subtype.ext hpq)
  · rintro ⟨⟨x,y⟩,hxy⟩
    obtain ⟨F,hF,_⟩ := unique_triangle_through_pair R hsym hirr hu x y hxy
    have hne : x≠y := by rintro rfl; exact hirr x hxy
    exact ⟨⟨F,⟨(x,y),Finset.mem_offDiag.mpr ⟨hF.1,hF.2,hne⟩⟩⟩,rfl⟩

end Atlas.Combinatorics
