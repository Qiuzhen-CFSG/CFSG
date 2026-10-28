module

public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.LatticeGenerators
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.TrialityGenerators

/-!
# Generator equivariance of the source triality–Leech comparison

Compose the actual conjugation calculation with the independent integral
Leech calculation. The source homomorphism intertwines `ψ₂(d)` with the
Golay sign isometry and `ψ₁(α)` with the coordinate permutation induced by
the standard automorphism, including either parity. The `ψ₁(d)` family
acts trivially. Conjugation is `g * q * g⁻¹` in Lean's left-composition
convention, on the genuine Parker triples with zero.

The last three equations express the same compatibility through the actual
quotients, first by `⟨k1⟩` and then by the center. The imported fixed
`naturalLeechComparison` intertwines these same Leech isometries with the
genuine signed halfspace transports, sending `L¹(x)` to the marked standard
basis vector. Thus the generator equations on the quadratic quotient and
the natural module use the same sign and permutation directions. Assembly
for the full `N1` action belongs to the local-group construction.

Source: Aschbacher, *Sporadic Groups*, Lemmas 23.10(4), 27.2 and 27.4,
printed pp. 120–121, 144–147, and the generator comparison on p. 148.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The first Parker family fixes the image of every element of `Q1`. -/
theorem sourceQ1LatticeHom_conjugation_psi1 (d : ParkerLoop) (q : Q1) :
    (sourceQ1LatticeHom (q1Conjugation ⟨psi1N d, psi1N_mem_N1 d⟩ q)).toAdd =
      (sourceQ1LatticeHom q).toAdd := by
  rw [sourceQ1LatticeHom_apply, q1Coordinates_conjugation_psi1,
    sourceQ1LatticeHom_apply]

/-- Actual conjugation by the second Parker family gives the Leech sign action. -/
theorem sourceQ1LatticeHom_conjugation_psi2 (d : ParkerLoop) (q : Q1) :
    (sourceQ1LatticeHom (q1Conjugation ⟨psi2N d, psi2N_mem_N1 d⟩ q)).toAdd =
      leechModTwoRepresentation (signIsometry d.1) (sourceQ1LatticeHom q).toAdd := by
  rw [sourceQ1LatticeHom_apply, q1Coordinates_conjugation_psi2,
    sourceCoordinateMap_sign, sourceQ1LatticeHom_apply]

/-- Every standard automorphism gives its actual Leech coordinate permutation. -/
theorem sourceQ1LatticeHom_conjugation_psiAut1 (α : ParkerStandardGroup) (q : Q1) :
    (sourceQ1LatticeHom (q1Conjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ q)).toAdd =
      leechModTwoRepresentation (permutationEmbedding (parkerStandardProjection α))
        (sourceQ1LatticeHom q).toAdd := by
  rw [sourceQ1LatticeHom_apply, q1Coordinates_conjugation_psiAut1,
    sourceCoordinateMap_permutation, sourceQ1LatticeHom_apply]

/-- The first-family equation through both actual quotient maps. -/
theorem sourceQ1QuotientLatticeIsometry_conjugation_psi1 (d : ParkerLoop) (q : Q1) :
    sourceQ1QuotientLatticeIsometry (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.center Q1Quotient)
        (QuotientGroup.mk' (K1.subgroupOf Q1)
          (q1Conjugation ⟨psi1N d, psi1N_mem_N1 d⟩ q)))) =
      sourceQ1QuotientLatticeIsometry (Additive.ofMul
        (QuotientGroup.mk' (Subgroup.center Q1Quotient)
          (QuotientGroup.mk' (K1.subgroupOf Q1) q))) := by
  simpa only [sourceQ1QuotientLatticeIsometry_mk] using
    sourceQ1LatticeHom_conjugation_psi1 d q

/-- The sign equation through both actual quotient maps, on every representative. -/
theorem sourceQ1QuotientLatticeIsometry_conjugation_psi2 (d : ParkerLoop) (q : Q1) :
    sourceQ1QuotientLatticeIsometry (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.center Q1Quotient)
        (QuotientGroup.mk' (K1.subgroupOf Q1)
          (q1Conjugation ⟨psi2N d, psi2N_mem_N1 d⟩ q)))) =
      leechModTwoRepresentation (signIsometry d.1)
        (sourceQ1QuotientLatticeIsometry (Additive.ofMul
          (QuotientGroup.mk' (Subgroup.center Q1Quotient)
            (QuotientGroup.mk' (K1.subgroupOf Q1) q)))) := by
  simpa only [sourceQ1QuotientLatticeIsometry_mk] using
    sourceQ1LatticeHom_conjugation_psi2 d q

/-- The permutation equation through both actual quotient maps, for either parity. -/
theorem sourceQ1QuotientLatticeIsometry_conjugation_psiAut1
    (α : ParkerStandardGroup) (q : Q1) :
    sourceQ1QuotientLatticeIsometry (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.center Q1Quotient)
        (QuotientGroup.mk' (K1.subgroupOf Q1)
          (q1Conjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ q)))) =
      leechModTwoRepresentation (permutationEmbedding (parkerStandardProjection α))
        (sourceQ1QuotientLatticeIsometry (Additive.ofMul
          (QuotientGroup.mk' (Subgroup.center Q1Quotient)
            (QuotientGroup.mk' (K1.subgroupOf Q1) q)))) := by
  simpa only [sourceQ1QuotientLatticeIsometry_mk] using
    sourceQ1LatticeHom_conjugation_psiAut1 α q

end Sporadic.Monster.Construction.LocalC
