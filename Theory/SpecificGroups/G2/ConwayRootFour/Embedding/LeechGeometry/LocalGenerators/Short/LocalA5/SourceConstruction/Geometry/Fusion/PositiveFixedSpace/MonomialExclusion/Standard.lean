module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Sextet

/-!
# Assembly of the standard-sextet quaternion exclusion

An actual monomial conjugator reducing the signed quaternion pair to the marked
reference pair transports its common binary fixed space. The explicit lattice
coordinate equivalence then transfers a lower bound of eight for the reference
common kernel, excluding dimension six. The proved pair normalization and
reference bound discharge both premises of the conditional assembly below.
The resulting theorem has the exact published standard-sextet contract,
including its scalar-origin hypothesis and centralization of the entire scalar A₄.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
with Lemma 47.2, p.261, and the root-four conventions on p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- Conjugation and the explicit lattice coordinates connect the two independent
calculations to the exact published standard-sextet contract. -/
theorem standardQuaternionExclusion_of_normalization_bound
    (hn : StandardQuaternionNormalization) (hr : ReferenceQuaternionBound) :
    StandardQuaternionExclusion := by
  intro a b m hstd ha hb hab hm hma hmb he _ho
  obtain ⟨r, hpair⟩ := hn a b hstd ha hb hab he
  let c (u : GolayMonomialGroup) := r * u * r⁻¹
  let t := monomialEmbedding r
  have hc (u : GolayMonomialGroup) : monomialEmbedding (c u) =
      t * monomialEmbedding u * t⁻¹ := by
    simp only [c, t, map_mul, map_inv]
  have hmc : monomialEmbedding (c m) ^ 2 = 1 := by
    rw [hc]
    calc
      (t * monomialEmbedding m * t⁻¹) ^ 2 = t * (monomialEmbedding m) ^ 2 * t⁻¹ := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hm]; group
  have hcomm (u : GolayMonomialGroup)
      (hu : Commute (monomialEmbedding m) (monomialEmbedding u)) :
      Commute (monomialEmbedding (c m)) (monomialEmbedding (c u)) := by
    rw [hc, hc]
    change _ * _ = _ * _
    calc
      (t * monomialEmbedding m * t⁻¹) * (t * monomialEmbedding u * t⁻¹) =
          t * (monomialEmbedding m * monomialEmbedding u) * t⁻¹ := by group
      _ = t * (monomialEmbedding u * monomialEmbedding m) * t⁻¹ := by rw [hu.eq]
      _ = (t * monomialEmbedding u * t⁻¹) * (t * monomialEmbedding m * t⁻¹) := by group
  have hd : Module.finrank Bit ↥(binaryFixed (monomialEmbedding a) ⊓
      binaryFixed (monomialEmbedding m)) =
      Module.finrank Bit ↥(binaryFixed (monomialEmbedding (c a)) ⊓
        binaryFixed (monomialEmbedding (c m))) := by
    have h := (commonFixedConjugate t⁻¹ (monomialEmbedding a) (monomialEmbedding m)).finrank_eq
    rw [inv_inv] at h
    rw [hc, hc]
    exact h
  have hbound := hr (c a) (c b) (c m) hpair hmc (hcomm a hma) (hcomm b hmb)
  rw [hd, StandardCoordinates.commonFixed_finrank]
  omega

/-- The common fixed space in the literal Leech quotient cannot have dimension
six for a signed quaternion pair on the standard Golay sextet. Both the
normalization and the reference kernel bound are discharged. -/
theorem standardQuaternionExclusion : StandardQuaternionExclusion :=
  standardQuaternionExclusion_of_normalization_bound
    standardQuaternionNormalization referenceQuaternionBound

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
