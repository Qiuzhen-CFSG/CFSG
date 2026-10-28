module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.Alternating.Aut

/-!
# Coordinates for the natural complement intersection

The centralizing element has trivial five-point coordinate. A point and root
frame records genuine SL₂(4) and vector equivalences, a displacement in the
three-point factor, and membership of the upper-1 root in the actual actor.
The remaining actor alternatives distinguish the full root group from an
outer field involution. In particular the component intersection is allowed
to have order two.

`PointRootNormalization` and `ActorNormalization` are mathematical obligations,
not assertions of their truth. They separate the geometric producers from
the invariant-form calculation and its source applications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.4.10, first proof paragraph, printed p.1010; 14.4.2(5), p.1006.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection

abbrev Bit := ZMod 2
abbrev Field := Representation.SL2FourNatural.F
abbrev Vector := Representation.SL2FourNatural.V
abbrev Special := Representation.SL2FourNatural.SL
abbrev Small := BinaryPermutation.core (Fin 3)
abbrev smallAction := BinaryPermutation.coreRepresentation (Fin 3)
abbrev e1 : Vector := ![1, 0]
abbrev e2 : Vector := ![0, 1]

open Representation.SL2FourNatural
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V]

/-- The component element in the specified SL₂(4) marking. -/
def componentActor (hAD : AltFive ≤ D) (e : AltFive ≃* Special) (a : Special) :
    Three × D := (1, inclusion hAD (e.symm a))

theorem componentActor_mem (e : AltFive ≃* Special) (a : Special) :
    componentActor hAD e a ∈ (⊥ : Subgroup Three).prod (AltFive.subgroupOf D) :=
  ⟨rfl, (e.symm a).property⟩

/-- Centralizing the actual alternating component kills the five-point coordinate. -/
theorem element_second_eq_one (hAD : AltFive ≤ D) {σ : Representation Bit D V}
    (d : ComplementIntersectionData σ) : d.element.2 = 1 := by
  apply Subtype.ext
  have h : d.element.2.val ∈ centralizer (AltFive : Set Five) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    have hh := mem_centralizer_iff.mp d.element_centralizes
      (1, inclusion hAD ⟨a, ha⟩) ⟨rfl, ha⟩
    exact congrArg (fun z : Three × D => z.2.val) hh
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at h
  exact h

/-- A genuine point/root coordinate frame. No form or perpendicularity equation
is imposed. The group and vector markings must intertwine the original action. -/
structure PointRootCoordinates {σ : Representation Bit D V}
    (hAD : AltFive ≤ D) (d : ComplementIntersectionData σ) where
  group : AltFive ≃* Special
  vector : V ≃ₗ[Bit] Vector
  equivariant : ∀ (a : AltFive) (v : V), vector (σ (inclusion hAD a) v) =
    action (group a) (vector v)
  small : Small
  preimage : Small
  displacement : smallAction d.element.1 preimage - preimage = small
  point_eq : d.point = small ⊗ₜ[Bit] vector.symm e1
  root_mem : componentActor hAD group (upper 1) ∈ d.actor

/-- The inner root group, or a commuting outer field actor in the normalized frame.
These clauses concern literal actor membership and its action on every vector. -/
def ActorAlternatives {σ : Representation Bit D V} {d : ComplementIntersectionData σ}
    (p : PointRootCoordinates hAD d) : Prop :=
  (∀ a : Field, componentActor hAD p.group (upper a) ∈ d.actor) ∨
  ∃ (a : D) (b : Field), (1, a) ∈ d.actor ∧ ∀ v : V,
    p.vector (σ a v) = action (upper b) (frobeniusLinear (p.vector v))

/-- The point/root normalization still to be constructed from the finite data. -/
def PointRootNormalization (hAD : AltFive ≤ D) (σ : Representation Bit D V) : Prop :=
  IsNaturalFour hAD σ → ∀ d : ComplementIntersectionData σ,
    Nonempty (PointRootCoordinates hAD d)

/-- The actor dichotomy in every genuine supplied point/root frame. -/
def ActorNormalization (hAD : AltFive ≤ D) (σ : Representation Bit D V) : Prop :=
  ∀ (d : ComplementIntersectionData σ) (p : PointRootCoordinates hAD d),
    ActorAlternatives p

variable {σ : Representation Bit D V}

theorem tensor_tmul (a : Three × D) (n : Small) (v : V) :
    sourceTensorAction σ a (n ⊗ₜ[Bit] v) = smallAction a.1 n ⊗ₜ[Bit] σ a.2 v := rfl

theorem PointRootCoordinates.component_equivariant (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (a : Special) (v : Vector) :
    σ (componentActor hAD p.group a).2 (p.vector.symm v) =
      p.vector.symm (action a v) := by
  apply p.vector.injective
  rw [p.vector.apply_symm_apply]
  change p.vector (σ (inclusion hAD (p.group.symm a)) (p.vector.symm v)) = _
  rw [p.equivariant, p.group.apply_symm_apply, p.vector.apply_symm_apply]

theorem PointRootCoordinates.first_tmul_mem (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (v : V) :
    p.small ⊗ₜ[Bit] v ∈ d.firstSpace := by
  rw [d.first_eq_range]
  refine ⟨p.preimage ⊗ₜ[Bit] v, ?_⟩
  change sourceTensorAction σ d.element (p.preimage ⊗ₜ[Bit] v) -
    p.preimage ⊗ₜ[Bit] v = _
  rw [tensor_tmul, element_second_eq_one hAD d, map_one, Module.End.one_apply,
    ← sub_tmul, p.displacement]

theorem PointRootCoordinates.second_tmul_mem (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (v : V) :
    smallAction InvertedCubicTensor.cubic p.small ⊗ₜ[Bit] v ∈ d.secondSpace := by
  rw [d.second_eq_translate]
  refine Submodule.mem_map.mpr ⟨_, p.first_tmul_mem d v, ?_⟩
  rw [tensor_tmul]
  change smallAction InvertedCubicTensor.cubic p.small ⊗ₜ[Bit] σ 1 v = _
  rw [map_one, Module.End.one_apply]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
end
