module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Sextet
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard

/-!
# The signed Golay quaternion fixed-space exclusion

Equal binary kernels force a genuine sextet. The established Golay sextet
transitivity theorem moves it to the six literal tetrads. Conjugating all three
monomial elements preserves the square relations, integral commutation,
equality of binary kernels, and their common fixed-space dimension. The scalar
origin witness is transported by the inverse frame change, preserving the
centralizer of the entire scalar A₄.

The proved standard-sextet calculation normalizes the signed pair to a literal
reference pair and bounds its common binary fixed space below by eight.
`monomialQuaternionExclusion` discharges that calculation in the reduction,
excluding dimension six with the full published scalar-origin hypothesis.
This supplies the finite input to the positive-square exclusion and its
placed-reflection application.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, with Lemma 47.2, p.261, and the root-four conventions on p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- A standard-sextet exclusion suffices for the original simultaneous
monomial frame, with no extra premise retained by the frame change. -/
theorem monomialQuaternionExclusion_of_standard
    (H : StandardQuaternionExclusion) : MonomialQuaternionExclusion := by
  intro a b m ha hb hab hm hma hmb he ho
  let S : UnorderedSextet := ⟨quaternionParts a b, quaternion_sextet a b ha hb hab he⟩
  obtain ⟨g, hg⟩ := sextet_equivalent_distinguished S
  let r : GolayMonomialGroup := SemidirectProduct.inr g
  let c : MulAut GolayMonomialGroup := MulAut.conj r
  let t := monomialEmbedding r
  let d : MulAut LeechIsometryGroup := MulAut.conj t
  have hmap (x : GolayMonomialGroup) : monomialEmbedding (c x) = d (monomialEmbedding x) := by
    simp only [c, d, MulAut.conj_apply, map_mul, map_inv, t]
  have hd (x : LeechIsometryGroup) : d x = t * x * t⁻¹ := rfl
  have hz : d negationIsometry = negationIsometry := by
    rw [hd, Subgroup.mem_center_iff.mp negation_mem_center t]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hstd : quaternionParts (c a) (c b) = distinguishedUnorderedSextet.val := by
    rw [show c a = r * a * r⁻¹ from rfl, show c b = r * b * r⁻¹ from rfl,
      quaternionParts_conjugate r a b]
    exact congrArg Subtype.val hg
  have he' : binaryFixed (monomialEmbedding (c a)) = binaryFixed (monomialEmbedding (c b)) := by
    simp only [hmap, hd]
    simpa only [inv_inv] using binaryFixed_conjugate_eq t⁻¹ _ _ he
  have ho' : ScalarOrigin (c a) (c b) (c m) := by
    obtain ⟨s, hsA, hsB, hsM⟩ := ho
    refine ⟨s * t⁻¹, ?_⟩
    have hrestore (x : GolayMonomialGroup) :
        (s * t⁻¹) * monomialEmbedding (c x) * (s * t⁻¹)⁻¹ = s * monomialEmbedding x * s⁻¹ := by
      rw [hmap, hd]
      group
    rw [hrestore, hrestore, hrestore]
    exact ⟨hsA, hsB, hsM⟩
  have hnew := H (c a) (c b) (c m) hstd
    (by rw [hmap, ← map_pow, ha, hz])
    (by rw [hmap, ← map_pow, hb, hz])
    (by rw [hmap, hmap, ← map_mul, ← map_pow, hab, hz])
    (by rw [hmap, ← map_pow, hm, map_one])
    (by rw [hmap, hmap]; exact hma.map d)
    (by rw [hmap, hmap]; exact hmb.map d) he' ho'
  have hdim := (commonFixedConjugate t⁻¹ (monomialEmbedding a) (monomialEmbedding m)).finrank_eq
  rw [hmap, hmap, hd, hd] at hnew
  rwa [hdim]

/-- A signed Golay quaternion pair with equal binary kernels and a commuting
square-one element has common fixed-space dimension different from six under
the published scalar-origin condition. The standard-sextet calculation is
discharged, leaving no additional premise. -/
theorem monomialQuaternionExclusion : MonomialQuaternionExclusion :=
  monomialQuaternionExclusion_of_standard standardQuaternionExclusion

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
