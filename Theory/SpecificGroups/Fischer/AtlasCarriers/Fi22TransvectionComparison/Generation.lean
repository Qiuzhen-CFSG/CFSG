module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Fiber
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Algebra
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges

/-!
# Assembly of the Fi22 commuting-conjugate certificate

The distinguished fiber and forward Schreier edges of the literal shared
conjugate words are certified. From the edge memberships we derive equivariance,
centralizing membership at fixed labels, exact coverage, and generation of the
actual relative centralizer. The final certificate has no additional premises
and supplies the centralizer branch of the transvection-action comparison.

Source: GLS3 Table 5.3t and its conjugation-action paragraph in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison

/-- The checked distinguished fiber leaves just the Schreier membership certificate. -/
theorem exists_commutingConjugate_certificate_of_edges
    (hedge : ∀ s ∈ atlasGenerators, ∀ x,
      (pointTransport (inclusion s x))⁻¹ * s * pointTransport x ∈
        commutingConjugateSubgroup) :
    ∃ hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA,
      Set.range (fixedPointRoot hc) = commutingConjugates ∧
        Subgroup.closure commutingConjugates = ⊤ := by
  have hroot := conjugateAt_equivariant_of_edges hedge
  have hfiber : ∀ x, conjugateAt x = atlasA → x = rootBase :=
    fun x => (conjugateAt_eq_atlasA_iff x).mp
  let hc := conjugateAt_centralizes_of_equivariant hroot
  refine ⟨hc, fixedPointRoot_range_of_fiber hfiber hroot hc, ?_⟩
  exact commutingConjugates_generate_of_edges pointTransport conjugateAt rootBase
    pointTransport_base conjugateAt_base hfiber hroot hedge

/-- The shared fixed-point roots are exactly all conjugates of `atlasA` in its
relative centralizer, and these conjugates generate that centralizer. -/
theorem exists_commutingConjugate_certificate :
    ∃ hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA,
      Set.range (fixedPointRoot hc) = commutingConjugates ∧
        Subgroup.closure commutingConjugates = ⊤ :=
  exists_commutingConjugate_certificate_of_edges
    schreierEdge_mem_commutingConjugateSubgroup

end Sporadic.Fischer.Fi22.TransvectionComparison
