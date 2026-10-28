module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Extension
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Coordinates for the deleted complement calculation

The normalized core vectors are the weight-four point, its weight-two
preimage, and a seed for that preimage. Two marked double transpositions
successively displace the seed to the preimage and the preimage to the point.
The selected centralizing element has trivial S₅ coordinate, by the trivial
centralizer of A₅ in S₅.

`PointNormalization` and `ActorGenerators` are separate, unproved geometric
obligations. Their definitions do not establish a normalization theorem.
The first concerns an arbitrary Sylow-fixed tensor point; the second concerns
relative normality of the actual elementary order-eight actor. They combine
into `Placement`, the input for the checked coordinate calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.4.2(5), printed p.1006, and 14.4.10, first proof paragraph, p.1010.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace Deleted

abbrev Core := BinaryPermutation.core (Fin 5)
abbrev Natural := BinaryPermutation.core (Fin 3)
abbrev permAction := BinaryPermutation.coreRepresentation (Fin 5)
abbrev naturalAction := BinaryPermutation.coreRepresentation (Fin 3)

def point : Core := ⟨![1,1,1,1,0], by rw [BinaryPermutation.mem_core]; decide⟩
def middle : Core := ⟨![1,1,0,0,0], by rw [BinaryPermutation.mem_core]; decide⟩
def seed : Core := ⟨![1,0,0,0,1], by rw [BinaryPermutation.mem_core]; decide⟩

abbrev first := BinaryPermutation.CubicFixedSpace.Five.first
abbrev second := BinaryPermutation.CubicFixedSpace.Five.second

theorem first_displacement : permAction first.val seed - seed = middle := by
  apply Subtype.ext
  decide

theorem second_displacement : permAction second.val middle - middle = point := by
  apply Subtype.ext
  decide

def conjugate (g : Five) (a : AltFive) : AltFive :=
  ⟨g * a.val * g⁻¹, (inferInstance : AltFive.Normal).conj_mem a.val a.property g⟩

def componentActor (hAD : AltFive ≤ D) (a : AltFive) : Three × D :=
  (1, inclusion hAD a)

theorem componentActor_mem (a : AltFive) : componentActor hAD a ∈
    (⊥ : Subgroup Three).prod (AltFive.subgroupOf D) := by
  exact ⟨rfl, a.property⟩

theorem element_second_eq_one (hAD : AltFive ≤ D) {σ : Representation (ZMod 2) D V}
    (d : ComplementIntersectionData σ) : d.element.2 = 1 := by
  apply Subtype.ext
  have h : d.element.2.val ∈ centralizer (AltFive : Set Five) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    have hh := mem_centralizer_iff.mp d.element_centralizes
      (componentActor hAD ⟨a, ha⟩) (componentActor_mem ⟨a, ha⟩)
    exact congrArg (fun z : Three × D => z.2.val) hh
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at h
  exact h

/-- Point coordinates and a natural-factor displacement preimage. No actor
placement, bilinear-form or commutator conclusion is asserted. -/
structure PointCoordinates {σ : Representation (ZMod 2) D V}
    (f : V ≃ₗ[ZMod 2] Core) (d : ComplementIntersectionData σ) where
  coordinate : Five
  natural : Natural
  preimage : Natural
  displacement : naturalAction d.element.1 preimage - preimage = natural
  point_eq : d.point = natural ⊗ₜ[ZMod 2] f.symm (permAction coordinate point)

/-- The same point coordinates, with the two marked Klein-four elements
proved to belong to the actual actor. -/
structure Placement {σ : Representation (ZMod 2) D V}
    (f : V ≃ₗ[ZMod 2] Core) (d : ComplementIntersectionData σ)
    extends PointCoordinates f d where
  first_mem : componentActor hAD (conjugate coordinate first) ∈ d.actor
  second_mem : componentActor hAD (conjugate coordinate second) ∈ d.actor

/-- The group-theoretic normalization obligation, with full equivariance
explicit so that it is independent of the extension-uniqueness proof. -/
def ActorPlacement (hAD : AltFive ≤ D) (σ : Representation (ZMod 2) D V) : Prop :=
  ∀ (f : V ≃ₗ[ZMod 2] Core),
    (∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v)) →
    ∀ d : ComplementIntersectionData σ, Nonempty (Placement (hAD := hAD) f d)

/-- Sylow-fixed point coordinates, independently of the actor placement. -/
def PointNormalization (σ : Representation (ZMod 2) D V) : Prop :=
  ∀ (f : V ≃ₗ[ZMod 2] Core),
    (∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v)) →
    ∀ d : ComplementIntersectionData σ, Nonempty (PointCoordinates f d)

/-- The two pure Klein-four elements belong to the actor in every supplied
point coordinate system. This retains relative normality as an input of d. -/
def ActorGenerators (hAD : AltFive ≤ D) (σ : Representation (ZMod 2) D V) : Prop :=
  ∀ (f : V ≃ₗ[ZMod 2] Core),
    (∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v)) →
    ∀ (d : ComplementIntersectionData σ) (p : PointCoordinates f d),
      componentActor hAD (conjugate p.coordinate first) ∈ d.actor ∧
      componentActor hAD (conjugate p.coordinate second) ∈ d.actor

variable {σ : Representation (ZMod 2) D V}

theorem PointCoordinates.natural_ne_zero
    (f : V ≃ₗ[ZMod 2] Core) (d : ComplementIntersectionData σ)
    (p : PointCoordinates f d) : p.natural ≠ 0 := by
  intro h
  apply d.point_ne_zero
  rw [p.point_eq, h, zero_tmul]

theorem actorPlacement_of_normalization (hpoint : PointNormalization σ)
    (hactor : ActorGenerators hAD σ) : ActorPlacement hAD σ := by
  intro f hf d
  obtain ⟨p⟩ := hpoint f hf d
  obtain ⟨ha, hb⟩ := hactor f hf d p
  exact ⟨{ toPointCoordinates := p, first_mem := ha, second_mem := hb }⟩

end Deleted
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
