/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway1.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.ConwaySimplicity
public import Theory.AtlasPort.OtherSporadic.Conway.CentralQuotientConstruction
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechConstruction

/-!
The actual Conway Co1 model as the central quotient of the Leech isometry group.
The proven cross geometry and normal-generation results give its order, simplicity, and faithful actions.

Source: Gerald Höhn, `Atlas/Sporadic/Conway1.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway1
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev Model := LeechCentralQuotient
abbrev Cover := LeechIsometryGroup
abbrev Crosses := LeechCross

def order : ℕ := 4157776806543360000

def projection : Cover →* Model := leechCentralProjection

def mathieu24Embedding : Mathieu24CodeModel →* Model := quotientPermutationEmbedding

def binaryRepresentation : Model →* (LeechModTwo ≃ₗ[Bit] LeechModTwo) :=
  quotientModTwoRepresentation

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model = order := leechCentralQuotient_order

theorem card_factorization : Nat.card Model = 2^21 * 3^9 * 5^4 * 7^2 * 11 * 13 * 23 := by
  rw [card]
  norm_num [order]

theorem isSimpleGroup : IsSimpleGroup Model := leechCentralQuotient_simple

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := leechCentralQuotient_noncommuting_pair

theorem perfect : Group.IsPerfect Model := leechCentralQuotient_perfect

theorem center : Subgroup.center Model = ⊥ := leechCentralQuotient_center

theorem normal_subgroups (L : Subgroup Model) [L.Normal] : L = ⊥ ∨ L = ⊤ :=
  leechCentralQuotient_normal_subgroups L

theorem cover_card : Nat.card Cover = 8315553613086720000 := leechIsometryGroup_order

theorem cover_not_simple : ¬ IsSimpleGroup Cover := leechIsometryGroup_not_simple

theorem projection_surjective : Function.Surjective projection := leechCentralProjection_surjective

theorem projection_kernel : projection.ker = Subgroup.center Cover := by
  rw [projection,leechCentralProjection_kernel,leechCentralSigns_eq_center]

theorem mathieu24Embedding_injective : Function.Injective mathieu24Embedding :=
  quotientPermutationEmbedding_injective

theorem degree : Nat.card Crosses = 8292375 := leechCross_card

theorem faithful : FaithfulSMul Model Crosses := quotient_cross_faithful

theorem primitive : MulAction.IsPreprimitive Model Crosses := quotient_cross_primitive

theorem binary_faithful : Function.Injective binaryRepresentation := quotientModTwoRepresentation_injective

structure CompleteConstruction : Prop where
  lattice : LeechConstruction
  central_quotient : ConwayCentralQuotientConstruction
  finite : Finite Model
  card : Nat.card Model = order
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  perfect : Group.IsPerfect Model
  cover_card : Nat.card Cover = 8315553613086720000
  cover_perfect : Group.IsPerfect Cover
  cover_nonsimple : ¬ IsSimpleGroup Cover
  full_cross_stabilizer : MulAction.stabilizer Cover standardCross = monomialSubgroup
  monomial_maximal : IsCoatom monomialSubgroup
  monomial_nonnormal : ¬ monomialSubgroup.Normal
  monomial_perfect : Group.IsPerfect monomialSubgroup
  projected_stabilizer : MulAction.stabilizer Model standardCross = quotientMonomialSubgroup
  projected_signs_normal : (quotientGolaySignSubgroup.subgroupOf quotientMonomialSubgroup).Normal
  projected_signs_abelian : IsMulCommutative quotientGolaySignSubgroup
  signs_generate_cover : Subgroup.normalClosure (golaySignSubgroup : Set Cover) = ⊤
  signs_generate_quotient : Subgroup.normalClosure (quotientGolaySignSubgroup : Set Model) = ⊤
  generated_by_monomial_and_zeta : generatedConwayGroup = ⊤
  sextet_isometry : SextetIsometryConstruction
  cross_degree : Nat.card Crosses = 8292375
  cross_faithful : FaithfulSMul Model Crosses
  cross_primitive : MulAction.IsPreprimitive Model Crosses
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = Subgroup.center Cover
  mathieu24_injective : Function.Injective mathieu24Embedding
  binary_injective : Function.Injective binaryRepresentation
  binary_compatible : ∀ g, binaryRepresentation (projection g) = leechModTwoRepresentation g
  cross_binary_compatible : ∀ g X, (quotientCrossRepresentation g X).val = binaryRepresentation g X.val

theorem construction : CompleteConstruction where
  lattice := leech_constructed
  central_quotient := conway_central_quotient_constructed
  finite := finite
  card := card
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  cover_card := cover_card
  cover_perfect := leechIsometryGroup_perfect
  cover_nonsimple := cover_not_simple
  full_cross_stabilizer := full_cross_stabilizer
  monomial_maximal := monomial_maximal
  monomial_nonnormal := monomial_not_normal
  monomial_perfect := monomialSubgroup_perfect
  projected_stabilizer := quotient_cross_stabilizer
  projected_signs_normal := quotientGolaySignSubgroup_normal
  projected_signs_abelian := quotientGolaySignSubgroup_abelian
  signs_generate_cover := golaySign_normalClosure_eq_full
  signs_generate_quotient := quotientGolaySigns_normalClosure_eq_full
  generated_by_monomial_and_zeta := generatedConwayGroup_eq_full
  sextet_isometry := sextet_isometry_constructed
  cross_degree := degree
  cross_faithful := faithful
  cross_primitive := primitive
  projection_surjective := projection_surjective
  projection_kernel := projection_kernel
  mathieu24_injective := mathieu24Embedding_injective
  binary_injective := binary_faithful
  binary_compatible := quotientModTwoRepresentation_compatible
  cross_binary_compatible := quotientCross_modTwo_equivariant

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.Conway1
