module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Reference
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Relations
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Orbit
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits

/-!
# The marked cubic under every icosian carrier equivalence

The existing exact presentation and generation theorem give one comparison
sending the two permutation generators to the concrete icosian pair.
A group-word identity sends its marked cubic to a conjugate of the reference.

The two checked generator-orbit theorems also show that every automorphism
of the permutation carrier preserves this cubic's conjugacy class: after
inner conjugation the first generator is fixed and the second is either
itself or its inverse. Inverting the second generator conjugates the cubic
by a*b⁻¹. Comparing an arbitrary supplied equivalence with the marked one
therefore proves the required actual conjugacy, with no assumption on the
choice of equivalence and no extra model-comparison premise.

Source: Aschbacher, *Sporadic Groups* (1994), the J₂ marking in 47.3 and
47.10, and the root J₂ choice in 49.1, p.280. The presentation is ATLAS
`J2G1-P2`; the imported literal permutation and icosian certificates retain
their ATLAS attribution and license.
-/

@[expose] public noncomputable section

open Atlas.Conway
open Sporadic.LeechRelated.J2
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open IcosianComparison.Generators

local notation "pairA" => IcosianComparison.Generators.x
local notation "pairB" => IcosianComparison.Generators.y

private def markedComparison : Carrier ≃* IcosianProjectiveModel :=
  IcosianComparison.comparisonOfGeneratingPair
    G2FourModule.Embedding.InnerRealization.PresentationExact.toCarrier_injective
    pairA pairB relations closure_pair_eq_top


private theorem markedComparison_a : markedComparison GeneratorPair.a = pairA :=
  IcosianComparison.comparisonOfGeneratingPair_a _ _ _ _ _

private theorem markedComparison_b : markedComparison GeneratorPair.b = pairB :=
  IcosianComparison.comparisonOfGeneratingPair_b _ _ _ _ _

private theorem inverse_word {G : Type*} [Group G] (a b : G) :
    (a * b⁻¹ * a * b) ^ 4 = MulAut.conj (a * b⁻¹) ((a * b * a * b⁻¹) ^ 4) := by
  rw [map_pow]
  apply congrArg (fun z : G => z ^ 4)
  change _ = (a * b⁻¹) * (a * b * a * b⁻¹) * (a * b⁻¹)⁻¹
  group

private theorem commutator_word {G : Type*} [Group G] (a b : G) (ha : a⁻¹ = a) :
    (a * b * a * b⁻¹) ^ 4 = MulAut.conj (b * a) ((a⁻¹ * b⁻¹ * a * b) ^ 4) := by
  rw [map_pow]
  apply congrArg (fun z : G => z ^ 4)
  change a * b * a * b⁻¹ = (b * a) * (a⁻¹ * b⁻¹ * a * b) * (b * a)⁻¹
  calc
    a * b * a * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by rw [ha]
    _ = (b * a) * (a⁻¹ * b⁻¹ * a * b) * (b * a)⁻¹ := by group

private theorem source_inverse_word :
    (GeneratorPair.a * GeneratorPair.b⁻¹ * GeneratorPair.a * GeneratorPair.b) ^ 4 =
      MulAut.conj (GeneratorPair.a * GeneratorPair.b⁻¹) RecognitionGeometry.x :=
  inverse_word _ _

private theorem source_cubic_automorphism (f : MulAut Carrier) :
    ∃ t : Carrier, f RecognitionGeometry.x = MulAut.conj t RecognitionGeometry.x := by
  obtain ⟨g, hga⟩ := GeneratorPair.first_generator_conjugate
    (f GeneratorPair.a) (f GeneratorPair.b) (GeneratorPair.pair_profile.map f)
  let k : MulAut Carrier := (MulAut.conj g)⁻¹ * f
  have hka : k GeneratorPair.a = GeneratorPair.a := by
    simp [k, MulAut.mul_apply, hga, mul_assoc]
  have hk : GeneratorPair.PairProfile GeneratorPair.a (k GeneratorPair.b) := by
    simpa only [hka] using GeneratorPair.pair_profile.map k
  obtain ⟨c, hca, hcb⟩ := GeneratorPair.second_generator_orbits (k GeneratorPair.b) hk
  have hf (z : Carrier) : f z = MulAut.conj g (k z) := by
    simp [k, MulAut.mul_apply, mul_assoc]
  rcases hcb with hcb | hcb
  · have hkx : k RecognitionGeometry.x = MulAut.conj c RecognitionGeometry.x := by
      simp only [RecognitionGeometry.x, map_pow, map_mul, map_inv, hka, hcb, hca]
    refine ⟨g * c, ?_⟩
    rw [hf, hkx, map_mul, MulAut.mul_apply]
  · have hkx : k RecognitionGeometry.x = MulAut.conj c
        ((GeneratorPair.a * GeneratorPair.b⁻¹ * GeneratorPair.a * GeneratorPair.b) ^ 4) := by
      simp only [RecognitionGeometry.x, map_pow, map_mul, map_inv, hka, hcb, hca, inv_inv]
    refine ⟨g * (c * (GeneratorPair.a * GeneratorPair.b⁻¹)), ?_⟩
    rw [hf, hkx, source_inverse_word]
    simp only [map_mul, MulAut.mul_apply]

private theorem referenceProjective_word :
    referenceProjective = (pairA⁻¹ * pairB⁻¹ * pairA * pairB) ^ 4 := by
  simp only [referenceProjective, referenceLift, map_pow, map_mul, map_inv,
    IcosianComparison.Generators.x, IcosianComparison.Generators.y]

private theorem markedComparison_cubic :
    markedComparison RecognitionGeometry.x = MulAut.conj
      (pairB * pairA) referenceProjective := by
  have hx : pairA ^ 2 = 1 := relations 0
  have hi : pairA⁻¹ = pairA :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  calc
    markedComparison RecognitionGeometry.x =
        (pairA * pairB *
          pairA * pairB⁻¹) ^ 4 := by
      simp only [RecognitionGeometry.x, map_pow, map_mul, map_inv,
        markedComparison_a, markedComparison_b]
    _ = MulAut.conj (pairB * pairA)
        ((pairA⁻¹ * pairB⁻¹ *
          pairA * pairB) ^ 4) :=
      commutator_word _ _ hi
    _ = MulAut.conj (pairB * pairA)
        referenceProjective := by rw [referenceProjective_word]

/-- The marked element is conjugate inside the actual projective icosian group. -/
theorem rootCubic_referenceConjugacy (e : Carrier ≃* IcosianProjectiveModel) :
    ∃ t : IcosianProjectiveModel,
      e RecognitionGeometry.x = MulAut.conj t referenceProjective := by
  let f : MulAut Carrier := e.trans markedComparison.symm
  obtain ⟨t, ht⟩ := source_cubic_automorphism f
  refine ⟨markedComparison t * (pairB * pairA), ?_⟩
  calc
    e RecognitionGeometry.x = markedComparison (f RecognitionGeometry.x) :=
      (markedComparison.apply_symm_apply _).symm
    _ = markedComparison (MulAut.conj t RecognitionGeometry.x) := by rw [ht]
    _ = MulAut.conj (markedComparison t) (markedComparison RecognitionGeometry.x) := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
    _ = MulAut.conj (markedComparison t) (MulAut.conj (pairB * pairA) referenceProjective) := by
      rw [markedComparison_cubic]
    _ = MulAut.conj (markedComparison t * (pairB * pairA)) referenceProjective := by
      simp only [map_mul, MulAut.mul_apply]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
