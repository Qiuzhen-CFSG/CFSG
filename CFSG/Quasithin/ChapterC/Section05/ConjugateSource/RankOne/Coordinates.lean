module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Coordinates for the natural conjugate-action indices

The quotient map below is defined on the actual embedded group U(L), with
kernel C_U(L). The Baumann action is the upper-unipotent action on a plane
over a finite field. Its parameter map has kernel C_S(U), on the full U.
Neither map assumes either of the indices to be computed.

The two mathematical steps are separated: C.5.4(2) supplies these
coordinates, and `Covers` proves that quotient fixed vectors are fixed
in the covering module. For an L₂-block, the action is
induced by S ∩ L; for an A₃-block the central layer is trivial.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),
printed p.155, and C.5.6 (*), printed p.156; I.2.3(1), printed p.413.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

open Subgroup
universe u
variable {G : Type u} [Group G]

/-- The literal commutator module of the selected block. -/
def U (L : Subgroup G) : Subgroup G := (ChapterC.blockU L).map L.subtype
noncomputable abbrev S (R : Subgroup G) : Subgroup G := ChapterB.baumann R
noncomputable abbrev Q (R L : Subgroup G) : Subgroup G := (L ⊔ S R).pCoreIn 2
noncomputable abbrev D (R L : Subgroup G) : Subgroup G := S R ⊓ centralizer (L : Set G)

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
cover. This is the covering-module property proved in `Covers` and transported
to S in `Lifting`. -/
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

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
