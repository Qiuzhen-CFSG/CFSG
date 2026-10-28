module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22CentralizerAction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22CentralizerKernel
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22UnitaryComparison
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary
public import Mathlib.GroupTheory.PGroup

/-!
# The unitary quotient of the Fi22 involution centralizer

The fixed-point action of the concrete ATLAS centralizer provides the quotient
map. An isomorphism of its image with the fixed projective SU₆(GF(4)) model
transports this map without changing its kernel. In particular this route does
not assert that the central double cover splits.

The checked involution and kernel certificates in `Fi22CentralizerKernel`,
together with the actual action comparison in `Fi22UnitaryComparison`,
discharge all premises of `exists_unitary_section`. Its numerator is the
whole centralizer of the first ATLAS generator, and its quotient map is the
fixed-point projection followed by the proved unitary equivalence.

This supplies the U₆(2) quotient section from the inner 2A centralizer
2U₆(2) in GLS3 Table 5.3t (`refs/KGroup/GLS3/Chapter5(sec3-).tex`), used
in Aschbacher--Smith A.2.19 (printed pp. 40–41, PDF pp. 51–52).
The downstream quasithin exclusion also requires the separate unitary rank bound.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22

open Theory.SpecificGroups

noncomputable def unitaryQuotient (e : FixedPointImage ≃* U6Two.Carrier) :
    centralizerA →* U6Two.Carrier := e.toMonoidHom.comp fixedPointProjection

theorem unitaryQuotient_surjective (e : FixedPointImage ≃* U6Two.Carrier) :
    Function.Surjective (unitaryQuotient e) :=
  e.surjective.comp fixedPointProjection_surjective

theorem unitaryQuotient_ker (e : FixedPointImage ≃* U6Two.Carrier) :
    (unitaryQuotient e).ker = fixedPointAction.ker := by
  exact (MonoidHom.ker_comp_of_injective fixedPointProjection e.toMonoidHom
    e.injective).trans fixedPointProjection_ker

theorem exists_unitary_section_of_fixedPointImage
    (ha : orderOf atlasA = 2)
    (hk : IsPGroup 2 fixedPointAction.ker)
    (e : FixedPointImage ≃* U6Two.Carrier) :
    ∃ (t : Carrier) (L : Subgroup Carrier) (f : L →* U6Two.Carrier),
      orderOf t = 2 ∧ L ≤ Subgroup.centralizer ({t} : Set Carrier) ∧
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  refine ⟨atlasA, centralizerA, unitaryQuotient e, ha, le_rfl,
    unitaryQuotient_surjective e, ?_⟩
  rwa [unitaryQuotient_ker]

/-- The actual ATLAS Fi22 carrier has an involution centralizer surjecting
onto the fixed projective SU₆(GF(4)) model with a 2-group kernel. -/
theorem exists_unitary_section :
    ∃ (t : Carrier) (L : Subgroup Carrier) (f : L →* U6Two.Carrier),
      orderOf t = 2 ∧ L ≤ Subgroup.centralizer ({t} : Set Carrier) ∧
      Function.Surjective f ∧ IsPGroup 2 f.ker :=
  exists_unitary_section_of_fixedPointImage orderOf_atlasA
    isPGroup_fixedPointAction_ker unitaryComparison

end Sporadic.Fischer.Fi22
