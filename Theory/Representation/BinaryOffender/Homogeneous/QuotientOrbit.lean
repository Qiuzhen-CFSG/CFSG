module

public import Theory.Representation.BinaryOffender.Homogeneous.Lift
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.Representation.RepEquiv

/-!
# Orbit spans in the literal central quotient

The canonical equivalence I/C_I(X) ≃ q(I) is equivariant. It therefore
preserves irreducibility, and equivariance of q also preserves commutator
spans and orbit spans. Consequently a homogeneous simple central image
lifts to a member of the exact `IsIrrPlusWith` family from A.1.40.

These are quotient-transport and lifting results for Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.40–42, printed pp.31–32.
The existence of the selected homogeneous image is a separate theorem.
-/

@[expose] public section

namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The canonical central-quotient equivalence intertwines the actual actions. -/
noncomputable def centralImageRepEquiv (X : Subgroup G) (I : Submodule (ZMod 2) V)
    (hI : X ≤ subspaceStabilizer ρ I) :
    RepEquiv (centralQuotientRepresentation ρ X I hI)
      (quotientImage ρ X I hI).toRepresentation where
  toLinearEquiv := centralQuotientImageEquiv ρ X I
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    exact centralQuotientImageEquiv_equivariant ρ X I hI x v

theorem quotientImage_irreducible {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) :
    IsIrreducible (quotientImage ρ X I hI.choose).toRepresentation :=
  (RepEquiv.irreducible_euqiv (centralImageRepEquiv ρ X I hI.choose)).mp hI.choose_spec.2

theorem quotientImage_full {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) :
    subspaceCommutator (fixedQuotientRepresentation ρ X)
      (I.map (fixedSpace ρ X).mkQ) ⊤ = I.map (fixedSpace ρ X).mkQ := by
  rw [← commutator_quotientImage, hI.choose_spec.1]

/-- The orbit span formed directly in the original central quotient. -/
noncomputable def centralOrbitSpan (X T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer X) (A : Submodule (ZMod 2) (V ⧸ fixedSpace ρ X)) :
    Submodule (ZMod 2) (V ⧸ fixedSpace ρ X) :=
  ⨆ t : T, A.map (normalizerQuotientRepresentation ρ X ⟨t,hT t.property⟩)

/-- Passing to the central quotient commutes with forming the orbit span. -/
theorem orbitSpan_quotientImage (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (I : Submodule (ZMod 2) V) :
    (orbitSpan ρ T I).map (fixedSpace ρ X).mkQ =
      centralOrbitSpan ρ X T hT (I.map (fixedSpace ρ X).mkQ) := by
  rw [orbitSpan, Submodule.map_iSup]
  apply iSup_congr
  intro t
  exact quotientImage_map_normalizer ρ X I ⟨t, hT t.property⟩

/-- A homogeneous simple image lifts to a genuine homogeneous Irr⁺ member.
This is a lifting theorem; the existence of the selected image is separate. -/
theorem commutatorLift_isIrrPlusWith {X T : Subgroup G}
    {W : Submodule (ZMod 2) V} {A : Subrepresentation (fixedQuotientRepresentation ρ X)}
    (hT : T ≤ Subgroup.normalizer X)
    (hA : A.toSubmodule ≤ W.map (fixedSpace ρ X).mkQ)
    (hfull : subspaceCommutator (fixedQuotientRepresentation ρ X) A.toSubmodule ⊤ =
      A.toSubmodule) (hirr : IsIrreducible A.toRepresentation)
    (hhom : homogeneousPart A (centralOrbitSpan ρ X T hT A.toSubmodule) = A.toSubmodule) :
    IsIrrPlusWith ρ X T (commutatorLift ρ X W A) := by
  let hs := subspaceCommutator_invariant ρ (centralPreimage ρ X W A) X
  refine ⟨hT, hs, commutatorLift_isIrrPlus ρ hA hfull hirr, ?_⟩
  have he : quotientImage ρ X (commutatorLift ρ X W A) hs = A :=
    Subrepresentation.toSubmodule_injective (commutatorLift_image ρ hA hfull)
  rw [he, orbitSpan_quotientImage ρ X T hT, commutatorLift_image ρ hA hfull]
  exact hhom
end Representation.BinaryOffender.Homogeneous
