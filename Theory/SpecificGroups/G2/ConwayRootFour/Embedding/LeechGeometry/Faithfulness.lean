module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.ScalarFour
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.Kernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.NegativeSquare

/-!
# Faithfulness of the tetrahedral centralizer on the Leech fixed space

The binary Klein-four argument bounds the restricted kernel's exponent by four,
so it suffices to rule out its involutions. A lift of such an involution to the
actual Leech isometry group squares either to the identity or to central
negation. The positive-square branch forces the lift to be a central sign;
the negative-square branch is impossible. Their proved lattice exclusions
therefore give `centralizerFaithful` for the literal scalar subgroup and quotient
action in `ScalarFour`, with no additional geometric premise.

This discharges the faithfulness input of
`LocalCoordinates.representation_injective`. Construction and marking of the
remaining local generators are separate obligations of the embedding assembly.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284, and the
scalar/root geometry of Section 48, p.269. The application is Aschbacher–Smith
I.2.2(5), printed p.411. The book first proves faithfulness for its local group
K₁; the lattice branches here prove the stronger full-centralizer kernel
assertion needed by the generated-group construction. No G₂ embedding,
root-four marking or centralizer identification is assumed.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry

/-- Actual lattice involutions and actual negative-square isometries are the
two geometric branches needed for faithfulness. Both hypotheses use the literal Leech
reduction representation, with the projective tetrahedral centralizer retained. -/
theorem centralizerFaithful_of_lattice_involutions
    (hpositive : ∀ h : LeechIsometryGroup,
      leechCentralProjection h ∈ centralizerI →
      (∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v) →
      h ^ 2 = 1 → h = 1 ∨ h = negationIsometry)
    (hnegative : ∀ h : LeechIsometryGroup,
      leechCentralProjection h ∈ centralizerI →
      (∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v) →
      h ^ 2 = negationIsometry → False) :
    CentralizerFaithful := by
  apply centralizerFaithful_of_involution_kernel
  intro g hg hfix htwo
  obtain ⟨h, rfl⟩ := leechCentralProjection_surjective g
  have hfix' : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v := by
    simpa only [quotientModTwoRepresentation_compatible] using hfix
  have hs : h ^ 2 ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel]
    apply MonoidHom.mem_ker.mpr
    simpa only [map_pow] using htwo
  rcases (leechCentralSigns_mem (h ^ 2)).mp hs with hs | hs
  · rcases hpositive h hg hfix' hs with rfl | rfl
    · exact map_one _
    · apply MonoidHom.mem_ker.mp
      rw [leechCentralProjection_kernel]
      exact (leechCentralSigns_mem _).mpr (Or.inr rfl)
  · exact (hnegative h hg hfix' hs).elim

/-- The full centralizer of the specified tetrahedral scalar subgroup acts
faithfully on the literal U-fixed subspace of the Leech lattice modulo two. -/
theorem centralizerFaithful : CentralizerFaithful :=
  centralizerFaithful_of_lattice_involutions positive_square_kernel negative_square_kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
