module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation

/-!
# Applying the two source presentation steps to marked actions

The conditional kernel equality from `PairPresentation` discharges the exact
presentation premise of `descendOfPairPresentation` and `ofPairActions`.
The all-root normal-form and Curtis--Tits transport obligations remain explicit,
as do the independent local actions on the E6 complementary space. The source
assembly owner must prove these obligations before claiming an unconditional
representation. Source: GLS3 §2.9.3 and Steinberg §3, Theorem 8, as used in
Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem WordDescent

variable (F : Type*) [Field F]

variable
  (hroot : (rootEvaluation F).ker ≤ rootPlaneRelationSubgroup F)
  (φ : RootWord F →* PairCompletion F)
  (hsimple : ∀ (s : Bool) (i : Fin 4) (t : F),
    φ (FreeGroup.of (signedRoot s i, t)) =
      pairQuotient F (FreeGroup.of (s, i, t)))
  (hplanes : ∀ (a b : typeF4Roots) (v : RootPlaneWord F a b),
    rootPlaneEvaluation F a b v = 1 → φ (rootPlaneInclusion F a b v) = 1)

/-- The two independent presentation inputs in the original generic descent. -/
def descendOfRootPlanes {G : Type*} [Group G]
    (ψ : Word F →* G)
    (ρ : ∀ i j : Fin 4, pairSubgroup F i j →* G)
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        ψ (FreeGroup.of (s, pairNode i j k, t))) : Cover F →* G :=
  descendOfPairPresentation F
    (ker_eq_pairRelationSubgroup_of_root_planes F hroot φ hsimple hplanes) ψ ρ hρ

@[simp] theorem descendOfRootPlanes_evaluation {G : Type*} [Group G]
    (ψ : Word F →* G)
    (ρ : ∀ i j : Fin 4, pairSubgroup F i j →* G)
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        ψ (FreeGroup.of (s, pairNode i j k, t))) (w : Word F) :
    descendOfRootPlanes F hroot φ hsimple hplanes ψ ρ hρ (coverEvaluation F w) = ψ w :=
  descendOfPairPresentation_evaluation F _ ψ ρ hρ w

/-- The source normal-form and transport results discharge the presentation
premise of the actual complementary-action constructor. -/
def ofPairActionsOfRootPlanes
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t)) :
    Cover F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  ofPairActions F
    (ker_eq_pairRelationSubgroup_of_root_planes F hroot φ hsimple hplanes) ρ hρ

@[simp] theorem ofPairActionsOfRootPlanes_simple
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t))
    (s : Bool) (i : Fin 4) (t : F) :
    ofPairActionsOfRootPlanes F hroot φ hsimple hplanes ρ hρ (coverSimple F s i t) =
      eigenspaceAction F (-1) (f4Simple F s i t) :=
  ofPairActions_simple F _ ρ hρ s i t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
