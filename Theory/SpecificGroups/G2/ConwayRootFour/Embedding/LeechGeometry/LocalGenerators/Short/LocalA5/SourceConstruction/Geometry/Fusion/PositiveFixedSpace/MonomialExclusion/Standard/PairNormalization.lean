module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.CoordinateOrbit
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.SignOrbit

/-!
# Assembly of signed standard-sextet pair normalization

The structural reduction identifies the two coordinate involutions with
pointwise independent hexacode translations. A coordinate orbit witness
conjugates them to the reference translations and transports all three square
relations and equality in Λ/2Λ. The sign orbit witness then gives a Golay sign
conjugator; composing the two actual group elements proves the exact published
normalization contract.

`standardQuaternionNormalization_of_orbits` retains the separate orbit interface.
`standardQuaternionNormalization` discharges both premises using the proved
coordinate and sign orbit theorems, establishing the exact normalization contract.
Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four conventions on p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
open PairNormalization

/-- The two finite orbit calculations imply the exact published normalization
contract. -/
theorem standardQuaternionNormalization_of_orbits
    (Hc : TranslationPairOrbit) (Hs : ReferenceSignOrbit) :
    StandardQuaternionNormalization := by
  intro a b hstd ha hb hab he
  obtain ⟨h,k,hh,hk,hne,hap,hbp⟩ := standard_pair_translations a b hstd ha hb hab
  obtain ⟨g,hga,hgb⟩ := Hc h k hh hk hne
  let r := hexMonomialLift g
  let c : MulAut GolayMonomialGroup := MulAut.conj r
  let t := monomialEmbedding r
  let d : MulAut LeechIsometryGroup := MulAut.conj t
  have hmap (x : GolayMonomialGroup) : monomialEmbedding (c x) = d (monomialEmbedding x) := by
    simp only [c,d,r,t,MulAut.conj_apply,map_mul,map_inv]
  have hz : d negationIsometry = negationIsometry := by
    change t * negationIsometry * t⁻¹ = negationIsometry
    rw [Subgroup.mem_center_iff.mp negation_mem_center t]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  have hsa : (monomialEmbedding (c a)) ^ 2 = negationIsometry := by
    rw [hmap,← map_pow,ha,hz]
  have hsb : (monomialEmbedding (c b)) ^ 2 = negationIsometry := by
    rw [hmap,← map_pow,hb,hz]
  have hsab : (monomialEmbedding (c a) * monomialEmbedding (c b)) ^ 2 = negationIsometry := by
    rw [hmap,hmap,← map_mul,← map_pow,hab,hz]
  have hpa (i : Omega) : monomialPull (c a) i = referencePullA i := by
    change monomialPull (hexMonomialLift g * a * (hexMonomialLift g)⁻¹) i = _
    rw [pull_conjugate_hexMonomialLift g a h.val hap,hga]
    rfl
  have hpb (i : Omega) : monomialPull (c b) i = referencePullB i := by
    change monomialPull (hexMonomialLift g * b * (hexMonomialLift g)⁻¹) i = _
    rw [pull_conjugate_hexMonomialLift g b k.val hbp,hgb]
    rfl
  have he' : binaryFixed (monomialEmbedding (c a)) = binaryFixed (monomialEmbedding (c b)) := by
    simp only [hmap,d,MulAut.conj_apply]
    simpa only [inv_inv] using binaryFixed_conjugate_eq t⁻¹ _ _ he
  obtain ⟨s,hpair⟩ := reference_pair_of_signOrbit Hs (c a) (c b) hpa hpb hsa hsb hsab he'
  refine ⟨signLift s * r,?_⟩
  have hc (x : GolayMonomialGroup) :
      signLift s * c x * (signLift s)⁻¹ =
        (signLift s * r) * x * (signLift s * r)⁻¹ := by
    change signLift s * (r * x * r⁻¹) * (signLift s)⁻¹ = _
    group
  rwa [hc,hc] at hpair

/-- Every signed quaternion pair on the standard sextet with equal fixed spaces
in the literal quotient Λ/2Λ has an actual simultaneous Golay monomial
conjugator to the reference pullbacks and signs. -/
theorem standardQuaternionNormalization : StandardQuaternionNormalization :=
  standardQuaternionNormalization_of_orbits translationPairOrbit referenceSignOrbit

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
