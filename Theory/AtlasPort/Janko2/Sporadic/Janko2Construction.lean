/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Janko2Construction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Sporadic.Janko2Structure
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechConstruction

/-!
# Janko2Construction

All integral, geometric, quotient, order, simplicity, and embedding clauses of the
Hall–Janko construction are assembled for the concrete projective icosian carrier.
Every field of the construction theorem is discharged by the proved lattice and group results.

Source: Gerald Höhn, `Atlas/Sporadic/Janko2Construction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

public section

noncomputable section
namespace Atlas.Sporadic.Janko2
open Atlas.Algebra Atlas.Lattices Atlas.Conway MulAction
open Atlas.Codes
open scoped commutatorElement BigOperators DirectSum

/-- Construction certificate for the actual quaternionic Leech centralizer
and its sign quotient. The linear cover and right scalar units remain distinct. -/
structure CompleteConstruction : Prop where
  leech : LeechConstruction
  integral_comparison : Nonempty (Lattice ≃ₗ[ℤ] Atlas.Lattices.leech)
  integral_rank : Module.finrank ℤ Lattice = 24
  integral_free : Module.Free ℤ Lattice
  integral_finite : Module.Finite ℤ Lattice
  quaternionic_rank : Module.finrank QuaternionAlgebraᵐᵒᵖ Coordinates = 3
  golden_rank : Module.finrank ScalarField Coordinates = 12
  rational_rank : Module.finrank ℚ Coordinates = 24
  lattice_onto : ∀ z : Coordinates,
    z ∈ rationalIcosianLattice ↔ latticeComparison z ∈ rationalLeech
  lattice_isometry : ∀ z w : Coordinates,
    rationalForm (latticeComparison z) (latticeComparison w) = icosianBilinear z w
  right_scalar_closed : ∀ a : Scalarᵐᵒᵖ, ∀ x : IcosianCoordinates,
    x ∈ icosianLeechModule → a • x ∈ icosianLeechModule
  integral_scalar_faithful : Function.Injective integralRightScalars
  integral_scalar_comparison : ∀ a : Scalarᵐᵒᵖ, ∀ x : Lattice,
    integralRightScalars a (integralComparison x) =
      integralComparison (icosianIntegralRightScalars a x)
  integral_scalar_units : ∀ u : RightScalarUnits, ∀ x : Atlas.Lattices.leech,
    integralRightScalars (MulOpposite.op (icosianNormOneToOrder (u⁻¹))) x =
      (rightScalarEmbedding u).val x
  full_glue_comparison : Nonempty ((Lattice ⧸ icosianLatticeTwice) ≃ₗ[Scalarᵐᵒᵖ]
    icosianMatrixGlue GoldenFour)
  glue_reduction : ∀ x : Lattice,
    (glueComparison (Submodule.Quotient.mk x)).val = fun i => icosianModuloTwo (x.val i)
  glue_card : Nat.card (Lattice ⧸ icosianLatticeTwice) = 4096
  axis_direct_sum : Nonempty ((Π i : Fin 3,icosianLatticeAxis i) ≃ₗ[Scalarᵐᵒᵖ]
    icosianTwiceCoordinates)
  axis_external_direct_sum : Nonempty ((⨁ i : Fin 3,icosianLatticeAxis i) ≃ₗ[Scalarᵐᵒᵖ]
    icosianTwiceCoordinates)
  axis_sum : (⨆ i : Fin 3,icosianLatticeAxis i) = icosianTwiceCoordinates
  full_centralizer : embedding.range = icosianCentralizer
  linear_comparison : Nonempty (LinearCover ≃* LeechCentralizer)
  linear_faithful : Function.Injective linearRepresentation
  cover_embedding : Function.Injective embedding
  scalar_center : Subgroup.center LinearCover = icosianCentralSigns
  center_card : Nat.card (Subgroup.center LinearCover) = 2
  linear_card : Nat.card LinearCover = 1209600
  finite : Finite Model
  card : Nat.card Model = 604800
  order : Nat.card Model = 2^7*3^3*5^2*7
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  perfect : Group.IsPerfect Model
  degree : Nat.card Points = 315
  faithful : FaithfulSMul Model Points
  primitive : IsPreprimitive Model Points
  projective_faithful : Function.Injective projectiveRepresentation
  projective_kernel : (toPermHom LinearCover QuaternionicPlane).ker = icosianCentralSigns
  point_kernel : (toPermHom LinearCover Points).ker = icosianCentralSigns
  frame_count : Nat.card Frames = 525
  frame_transitive : IsPretransitive LinearCover Frames
  frame_size : ∀ F : Frames, F.val.card = 3
  frame_orthogonal : ∀ F : Frames, ∀ p q : Points,
    incident p F → incident q F → p ≠ q → orthogonal p q
  full_frame_stabilizer : stabilizer LinearCover baseFrame = icosianCoordinateFrameStabilizer
  frame_stabilizer_card : Nat.card FrameStabilizer = 2304
  orthogonal_count : ∀ p : Points, Nat.card (IcosianRootNeighbors p) = 10
  orthogonal_completion : ∀ p q : Points, orthogonal p q →
    ∃! r : Points, orthogonal p r ∧ orthogonal q r
  reflection_square : ∀ p : Points, reflection p * reflection p = 1
  reflection_order : ∀ p : Points, orderOf (reflection p) = 2
  local_reflection_card : ∀ p : Points, Nat.card (icosianProjectiveLineInvolutions p) = 2
  local_reflection_central : ∀ p : Points,
    (icosianProjectiveLineInvolutions p).subgroupOf (stabilizer Model p) ≤
      Subgroup.center (stabilizer Model p)
  reflection_conjugate : ∀ g : Model, ∀ p : Points,
    g * reflection p * g⁻¹ = reflection (g • p)
  reflection_generation : Subgroup.closure (Set.range reflection) = ⊤
  full_reflection_generation : icosianReflectionGroup = ⊤
  frame_commutator :
    ⁅icosianProjectiveAxisCycle,icosianProjectiveAxisReflection 0⁆ =
      icosianProjectiveAxisReflection 2
  primitive_arithmetic : ∀ T : Finset (Fin 6), 0 ∈ T →
    (∑ i ∈ T,icosianRootSubdegree i) ∣ 315 →
      (∑ i ∈ T,icosianRootSubdegree i) = 1 ∨ (∑ i ∈ T,icosianRootSubdegree i) = 315
  iwasawa_local : ∀ p : Points,
    icosianProjectiveLineInvolutions p ≤ stabilizer Model p
  iwasawa_normal : ∀ p : Points,
    ((icosianProjectiveLineInvolutions p).subgroupOf (stabilizer Model p)).Normal
  iwasawa_abelian : ∀ p : Points, IsMulCommutative (icosianProjectiveLineInvolutions p)
  iwasawa_generation : ∀ p : Points,
    Subgroup.normalClosure (icosianProjectiveLineInvolutions p : Set Model) = ⊤
  angle_invariant : ∀ g : Model, ∀ p q : Points, angle (g • p) (g • q) = angle p q
  angle_values_distinct : Function.Injective angleValue
  angle_exhaustive : ∀ p q : Points, ∃ i : Fin 6, angle p q = angleValue i
  angle_card : ∀ p : Points, ∀ i : Fin 6,
    Nat.card {q : Points // angle p q=angleValue i} = subdegree i
  angle_stabilizer_orbit : ∀ p q : Points,
    orbit (stabilizer Model p) q = {r : Points | angle p r = angle p q}
  suborbit_card : ∀ i : Fin 6, Nat.card (suborbit i) = subdegree i
  suborbit_cover : ∀ p : Points, ∃ i : Fin 6, p ∈ suborbit i
  suborbit_pairwise : Pairwise (fun i j => Disjoint (suborbit i) (suborbit j))
  suborbit_orbits : ∀ i : Fin 6, ∀ p : Points, p ∈ suborbit i →
    orbit (stabilizer Model basePoint) p = suborbit i
  quotient_surjective : Function.Surjective projection
  co1_injective : Function.Injective toConway1
  co1_compatible : ∀ g : LinearCover,
    toConway1 (projection g) = leechCentralProjection (embedding g)
  right_scalar_card : Nat.card RightScalarUnits = 120
  scalar_intersection : rightScalarEmbedding.range ⊓ icosianCentralizer = leechCentralSigns
  scalar_commutation : ∀ u : RightScalarUnits, ∀ g : LinearCover,
    Commute (rightScalarEmbedding u) (embedding g)
  central_product_kernel : ∀ u : RightScalarUnits, ∀ g : LinearCover,
    (u,g) ∈ icosianScalarCentralProduct.ker ↔
      (u=1 ∧ g=1) ∨ (u=icosianNormOneMinusOne ∧ g=icosianCentralSign)
  central_product_injective : Function.Injective icosianCentralProductToCo0
  scalar_alternating_comparison : Nonempty (IcosianScalarProjectiveModel ≃* alternatingGroup (Fin 5))
  alternating_product_injective : Function.Injective alternatingProductToConway1

theorem construction : CompleteConstruction where
  leech := leech_constructed
  integral_comparison := ⟨integralComparison⟩
  integral_rank := integral_rank
  integral_free := integral_free
  integral_finite := integral_finite
  quaternionic_rank := quaternionic_rank
  golden_rank := golden_rank
  rational_rank := rational_rank
  lattice_onto := lattice_comparison_onto
  lattice_isometry := lattice_comparison_isometry
  right_scalar_closed := right_scalar_closed
  integral_scalar_faithful := integralRightScalars_injective
  integral_scalar_comparison := integralRightScalars_comparison
  integral_scalar_units := integralRightScalars_unit
  full_glue_comparison := ⟨glueComparison⟩
  glue_reduction := glue_comparison_reduction
  glue_card := glue_quotient_card
  axis_direct_sum := ⟨axisDirectSumComparison⟩
  axis_external_direct_sum := ⟨axisExternalDirectSumComparison⟩
  axis_sum := lattice_axes_sum
  full_centralizer := full_centralizer
  linear_comparison := ⟨linearComparison⟩
  linear_faithful := linear_faithful
  cover_embedding := embedding_injective
  scalar_center := center
  center_card := center_card
  linear_card := linear_card
  finite := finite
  card := card
  order := order
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  degree := degree
  faithful := faithful
  primitive := primitive
  projective_faithful := quaternionic_projective_faithful
  projective_kernel := quaternionic_projective_kernel
  point_kernel := point_kernel
  frame_count := frame_count
  frame_transitive := frame_transitive
  frame_size := frame_size
  frame_orthogonal := frame_orthogonal
  full_frame_stabilizer := full_frame_stabilizer
  frame_stabilizer_card := frame_stabilizer_card
  orthogonal_count := orthogonal_count
  orthogonal_completion := orthogonal_completion
  reflection_square := reflection_square
  reflection_order := reflection_order
  local_reflection_card := local_reflection_card
  local_reflection_central := local_reflection_central
  reflection_conjugate := reflection_conjugate
  reflection_generation := reflection_generation
  full_reflection_generation := full_reflection_generation
  frame_commutator := icosianProjective_frame_commutator
  primitive_arithmetic := icosian_six_suborbit_block_arithmetic
  iwasawa_local := icosianProjectiveLineInvolutions_le_stabilizer
  iwasawa_normal := icosianProjectiveLineInvolutions_normal
  iwasawa_abelian := icosianProjectiveLineInvolutions_abelian
  iwasawa_generation := icosianProjectiveLineInvolutions_normalClosure
  angle_invariant := angle_invariant
  angle_values_distinct := angle_values_injective
  angle_exhaustive := angle_exhaustive
  angle_card := angle_card
  angle_stabilizer_orbit := angle_stabilizer_orbit
  suborbit_card := suborbit_card
  suborbit_cover := suborbit_cover
  suborbit_pairwise := suborbit_pairwise
  suborbit_orbits := suborbit_is_orbit
  quotient_surjective := projection_surjective
  co1_injective := toConway1_injective
  co1_compatible := toConway1_compatible
  right_scalar_card := right_scalar_card
  scalar_intersection := scalar_intersection
  scalar_commutation := scalar_commutation
  central_product_kernel := central_product_kernel
  central_product_injective := central_product_injective
  scalar_alternating_comparison := ⟨scalarAlternatingComparison⟩
  alternating_product_injective := alternatingProductToConway1_injective

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G=604800 ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.Janko2
