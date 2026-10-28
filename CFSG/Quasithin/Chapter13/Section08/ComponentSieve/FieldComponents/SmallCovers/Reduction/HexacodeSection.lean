module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Quotient
public import Theory.Representation.HexacodeAction.Field

/-!
# Marking the actual six-dimensional section

`HexacodeSection` is the outstanding recognition target, not an assumed
source theorem. It specifies a proper invariant denominator in the actual
U_H/V₁, zero in the whole-module case, otherwise a six-dimensional Irr⁺
submodule. Its actor is a faithful map from the actual H/O₂(H), maps K*
onto the genuine even hexacode cover, and intertwines the quotient action
with the concrete binary hexacode action.

From such a recognition, the quotient and seed lemmas prove that a maximal
local parabolic is precisely the stabilizer of the surviving binary plane.
When the cubic scalar lies in that parabolic, the plane is an actual
one-dimensional F₄-submodule. The field structure and scalar calculation
are from the existing attributed hexacode port. The conclusion retains the
actual quotient projection, coordinates and relative stabilizer, rather
than assuming a marked point.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.21(2), printed p.956 (PDF p.973), using B.4.2(8), B.4.5 and F.9.18(6).
Constructing `HexacodeSection` from those earlier results, and establishing
the maximal parabolic and scalar placement, remain reduction obligations.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
variable {G : Type*} [Group G]
variable (H K V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Recognition data to be constructed from the earlier module theorems.
The representation is on a literal quotient, with an explicit intertwiner. -/
structure HexacodeSection (act : QuotientAction H V₃ V₁) where
  denominator : Subrepresentation act.representation
  proper : denominator ≠ ⊤
  denominator_kind : denominator = ⊥ ∨
    (IsIrrPlus act.representation (Source.starImage H K) denominator.toSubmodule ∧
      Module.finrank (ZMod 2) denominator.toSubmodule = 6)
  actor : Source.Hstar H →* HexAutomorphisms
  actor_injective : Function.Injective actor
  component_image : (Source.starImage H K).map actor = hexSign.ker
  equivalence : ((Additive (Source.Utilde H V₃ V₁)) ⧸ denominator.toSubmodule) ≃ₗ[ZMod 2]
    hexacode
  intertwines : ∀ h v, equivalence (denominator.quotientRepresentation h v) =
    Hexacode.action (actor h) (equivalence v)

variable {H K V₃ V₁}
variable (act : QuotientAction H V₃ V₁) (s : HexacodeSection H K V₃ V₁ act)

theorem HexacodeSection.finrank : Module.finrank (ZMod 2)
    ((Additive (Source.Utilde H V₃ V₁)) ⧸ s.denominator.toSubmodule) = 6 :=
  s.equivalence.finrank_eq.trans hexacode_finrank

def HexacodeSection.seed : Submodule (ZMod 2) hexacode :=
  ((seedSpace H V₃ V₁).map s.denominator.toSubmodule.mkQ).map s.equivalence.toLinearMap

theorem HexacodeSection.seed_finrank
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2) :
    Module.finrank (ZMod 2) (s.seed act) = 2 := by
  rw [HexacodeSection.seed, s.equivalence.finrank_map_eq]
  exact quotient_seed_finrank H V₃ V₁ act P hP s.denominator s.proper hseed

theorem HexacodeSection.stabilizer_comap :
    (subspaceStabilizer Hexacode.action (s.seed act)).comap s.actor =
      subspaceStabilizer s.denominator.quotientRepresentation
        ((seedSpace H V₃ V₁).map s.denominator.toSubmodule.mkQ) := by
  ext g
  change (∀ v, Hexacode.action (s.actor g) v ∈ s.seed act ↔ v ∈ s.seed act) ↔ _
  have he (w) : s.equivalence w ∈ s.seed act ↔
      w ∈ (seedSpace H V₃ V₁).map s.denominator.toSubmodule.mkQ := by
    constructor
    · rintro ⟨v, hv, hvw⟩
      exact s.equivalence.injective hvw ▸ hv
    · intro hw
      exact ⟨w, hw, rfl⟩
  constructor
  · intro h v
    simpa only [← s.intertwines, he] using h (s.equivalence v)
  · intro h v
    obtain ⟨w, rfl⟩ := s.equivalence.surjective v
    rw [← s.intertwines, he, he]
    exact h w

/-- Construct the F₄-point and its marked stabilizer from the surviving
seed, maximality and the actual cubic scalar. -/
theorem HexacodeSection.marked_point
    (P : Subgroup G) (hP : P ≤ normalizer (V₃ : Set G))
    (hmax : IsCoatom (Source.starImage H P))
    [IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation]
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hscalar : hexZ ∈ (Source.starImage H P).map s.actor) :
    ∃ D : Submodule Hexacode.F hexacode,
      Module.finrank Hexacode.F D = 1 ∧ D.restrictScalars (ZMod 2) = s.seed act ∧
      (subspaceStabilizer Hexacode.action (D.restrictScalars (ZMod 2))).comap s.actor =
        Source.starImage H P := by
  have hmark : (subspaceStabilizer Hexacode.action (s.seed act)).comap s.actor =
      Source.starImage H P := by
    rw [s.stabilizer_comap act]
    exact quotient_seed_stabilizer H V₃ V₁ act P hP hmax s.denominator s.proper
      hseed (s.finrank act)
  have hz : hexZ ∈ subspaceStabilizer Hexacode.action (s.seed act) := by
    obtain ⟨z, hz, he⟩ := hscalar
    rw [← he]
    exact (show z ∈ (subspaceStabilizer Hexacode.action (s.seed act)).comap s.actor
      from hmark ▸ hz)
  refine ⟨Hexacode.scalarSubmodule (s.seed act) hz, ?_, rfl, hmark⟩
  have hd := Hexacode.scalarSubmodule_finrank (s.seed act) hz
  rw [s.seed_finrank act P hP hseed] at hd
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
