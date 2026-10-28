module

public import Theory.Representation.BinaryOffender.Homogeneous.Existence

/-!
# Homogeneous selection preserving the constituent type

A normalizing two-group orbit of an Irr⁺ member contains a homogeneous
Irr⁺ member with the same module type modulo the fixed space. Homogeneous
selection first produces an isomorphic simple central image. Its canonical
commutator lift has exactly that image, so the original equivariant
isomorphism survives the lift.

This strengthens the existence result by retaining its constituent-type
witness, as required when applying the selection to a prescribed module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Lemma A.1.42, printed p.32; the type-preserving
application appears in Lemma 3.2.3.
-/

@[expose] public section

namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The selected homogeneous member has the same actual `X`-module type
as the given Irr⁺ member after taking the central images. -/
theorem exists_isIrrPlusWith_le_orbitSpan_sameModule [FiniteDimensional (ZMod 2) V]
    {X T : Subgroup G} (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    ∃ J : Submodule (ZMod 2) V, J ≤ orbitSpan ρ T I ∧
      ∃ hJ : IsIrrPlusWith ρ X T J,
        SameModule (quotientImage ρ X I hI.choose) (quotientImage ρ X J hJ.invariant) := by
  obtain ⟨A, he, hA, hirr, hfull, hhom⟩ := exists_homogeneous_centralImage ρ hT hP
    (quotientImage ρ X I hI.choose) (quotientImage_irreducible ρ hI)
    (quotientImage_full ρ hI)
  have hle : A.toSubmodule ≤ (orbitSpan ρ T I).map (fixedSpace ρ X).mkQ := by
    rwa [orbitSpan_quotientImage ρ X T hT]
  have hJ := commutatorLift_isIrrPlusWith ρ hT hle hfull hirr hhom
  refine ⟨commutatorLift ρ X (orbitSpan ρ T I) A,
    commutatorLift_le ρ (orbitSpan_component_invariant ρ hT hI) A, hJ, ?_⟩
  have himage : quotientImage ρ X (commutatorLift ρ X (orbitSpan ρ T I) A)
      hJ.invariant = A :=
    Subrepresentation.toSubmodule_injective (commutatorLift_image ρ hle hfull)
  rwa [himage]

end Representation.BinaryOffender.Homogeneous
