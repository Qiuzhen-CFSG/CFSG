module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.Inputs

/-!
# Coordinates for the natural conjugate-action indices

The quotient map below is defined on the actual embedded group U(L), with
kernel C_U(L). The Baumann action is the upper-unipotent action on a plane
over a finite field. Its parameter map has kernel C_S(U), on the full U.
Neither map assumes either of the indices to be computed.

The two remaining source inputs are separated: C.5.4(2) constructs these
coordinates, and the rank-one part of I.2.3 proves that quotient fixed
vectors are fixed in the covering module. For an L₂-block, the action is
induced by S ∩ L; for an A₃-block the central layer is trivial.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),
printed p.155, and C.5.6 (*), printed p.156; I.2.3(1), printed p.413.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

open Subgroup
universe u
variable {G : Type u} [Group G]

/-- Literal conjugation on the embedded module. -/
def moduleConjugate {R L : Subgroup G}
    (hn : S R ≤ normalizer (U L : Set G)) (s : S R) (v : U L) : U L :=
  ⟨(s : G) * (v : G) * (s : G)⁻¹,
    (mem_normalizer_iff.mp (hn s.property) (v : G)).mp v.property⟩

/-- The natural plane quotient and its actual upper-unipotent Baumann action.
The projection need not be injective: U may have a nontrivial central layer. -/
structure ActionCoordinates (R L : Subgroup G) (F : Type*) [Field F] where
  normalizes : S R ≤ normalizer (U L : Set G)
  parameter : S R →* Multiplicative F
  parameter_surjective : Function.Surjective parameter
  parameter_kernel : ∀ s : S R,
    parameter s = 1 ↔ (s : G) ∈ centralizer (U L : Set G)
  projection : U L →* Multiplicative (Fin 2 → F)
  projection_surjective : Function.Surjective projection
  projection_kernel : ∀ v : U L,
    projection v = 1 ↔ (v : G) ∈ centralizer (L : Set G)
  equivariant : ∀ (s : S R) (v : U L),
    (projection (moduleConjugate normalizes s v)).toAdd =
      ![(projection v).toAdd 0 + (parameter s).toAdd * (projection v).toAdd 1,
        (projection v).toAdd 1]

/-- The full action is induced by the intersection with L, as in C.5.4(2). -/
def ActionCoordinates.IsInternal {R L : Subgroup G} {F : Type*} [Field F]
    (c : ActionCoordinates R L F) : Prop :=
  ∀ s : S R, ∃ t : S R, (t : G) ∈ L ∧ c.parameter t = c.parameter s

/-- Fixed vectors in the natural quotient lift to fixed vectors in the full
cover. This is a remaining covering-module assertion, not a field definition. -/
def ActionCoordinates.FixedLift {R L : Subgroup G} {F : Type*} [Field F]
    (c : ActionCoordinates R L F) : Prop :=
  ∀ (s : S R) (v : U L),
    c.projection (moduleConjugate c.normalizes s v) = c.projection v →
      moduleConjugate c.normalizes s v = v

/-- The precise intrinsic covering fact needed from I.2.3 in rank one. -/
def LinearCoverInput : Prop :=
  ∀ (L : Subgroup G) (n : ℕ), ChapterC.IsL2EvenBlock L n →
    ∀ (l : L) (v : ChapterC.blockU L),
      QuotientGroup.mk' (ChapterC.blockFixed L) (ChapterC.blockConjugate L l v) =
        QuotientGroup.mk' (ChapterC.blockFixed L) v →
      ChapterC.blockConjugate L l v = v

/-- The A₃ commutator module has no central layer; unlike a natural L₂-cover,
it has no nonsplit extension by a trivial module. -/
def AlternatingThreeCoverInput : Prop :=
  ∀ L : Subgroup G, ChapterC.IsAlternatingBlock L 3 → ChapterC.blockFixed L = ⊥

variable [Finite G]

/-- C.5.4(2), retaining the plane action and the internal actor for an L₂-block. -/
def LinearCoordinatesInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ∀ n, ChapterC.IsL2EvenBlock L n →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        ∃ c : ActionCoordinates R L F, c.IsInternal

/-- The A₃ branch uses the natural binary plane and its order-two actor.
The central-layer premise permits construction independently of its proof;
the assembly supplies it from `AlternatingThreeCoverInput`. -/
def AlternatingThreeCoordinatesInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 3 → ChapterC.blockFixed L = ⊥ →
      Nonempty (ActionCoordinates R L (ZMod 2))

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

end
