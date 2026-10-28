/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Construction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Simplicity
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechConstruction
/-!
The full norm-six Leech-vector stabilizer construction of Conway Co₃.
The final theorem assembles the proved order, faithful actions, triangle geometry, and simplicity.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Construction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway
set_option maxRecDepth 10000

theorem complement_free : Module.Free ℤ Complement := inferInstance

theorem complement_finite : Module.Finite ℤ Complement := inferInstance

theorem antipodalStabilizerEquiv_compatible (g : Model) :
    (antipodalStabilizerEquiv g).val = toConway1 g := rfl

theorem triangleMathieuEquiv_compatible (g : Mathieu23PointModel co3MarkedCoordinate) :
    (triangleMathieuEquiv g).val = mathieu23Embedding g := rfl

theorem mathieu23Embedding_range : mathieu23Embedding.range = TriangleStabilizer := by
  ext g
  constructor
  · rintro ⟨p,rfl⟩
    exact (triangleMathieuEquiv p).prop
  · intro hg
    obtain ⟨p,hp⟩ := triangleMathieuEquiv.surjective ⟨g,hg⟩
    exact ⟨p,congrArg Subtype.val hp⟩

/-- Complete construction on the full norm-six stabilizer in the retained Golay Leech lattice. -/
structure CompleteConstruction : Prop where
  lattice : LeechConstruction
  norm : integerDot vector.val.val vector.val.val = 48
  finite : Finite Model
  card : Nat.card Model = order
  factorization : Nat.card Model = 2^10 * 3^7 * 5^3 * 7 * 11 * 23
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  cover_injective : Function.Injective embedding
  quotient_injective : Function.Injective toConway1
  quotient_compatible : ∀ g, (antipodalStabilizerEquiv g).val = toConway1 g
  shell_card : Nat.card (LeechShell 6) = 16773120
  shell_transitive : MulAction.IsPretransitive LeechIsometryGroup (LeechShell 6)
  shell_index : 16773120 * Nat.card Model = Nat.card LeechIsometryGroup
  line_index : 8386560 * Nat.card Model = Nat.card LeechCentralQuotient
  complement_rank : Module.finrank ℤ Complement = 23
  complement_free : Module.Free ℤ Complement
  complement_finite : Module.Finite ℤ Complement
  integral_faithful : Function.Injective integralRepresentation
  integral_isometric : ∀ g x y,
    integerDot (integralRepresentation g x).val.val (integralRepresentation g y).val.val =
      integerDot x.val.val y.val.val
  degree : Nat.card Points = 276
  faithful : FaithfulSMul Model Points
  doubly_transitive : MulAction.IsMultiplyPretransitive Model Points 2
  primitive : MulAction.IsPreprimitive Model Points
  point_heptad_equivariant : ∀ g p,
    pointHeptadEquiv (co3PointHeptadMap co3MarkedCoordinate g p) = mathieu23Embedding g • pointHeptadEquiv p
  point_stabilizer_order : Nat.card PointStabilizer = 1796256000
  point_stabilizer_transitive : MulAction.IsPretransitive PointStabilizer (SubMulAction.ofStabilizer Model basePoint)
  mathieu_injective : Function.Injective mathieu23Embedding
  mathieu_full : mathieu23Embedding.range = TriangleStabilizer
  mathieu_order : Nat.card TriangleStabilizer = 10200960
  mathieu_maximal : IsCoatom TriangleStabilizer
  triangle_degree : Nat.card Triangles = 48600
  triangle_transitive : MulAction.IsPretransitive Model Triangles
  triangle_primitive : MulAction.IsPreprimitive Model Triangles
  triangle_full_stabilizer : MulAction.stabilizer Model baseTriangle = TriangleStabilizer
  triangle_subdegrees : ∀ t : Fin 8,
    Nat.card {y : Triangles // triangleType y = t} = ![1,253,506,1771,7590,8855,14168,15456] t
  triangle_orbits : ∀ x y : Triangles,
    (∃ g : Mathieu23PointModel co3MarkedCoordinate, mathieu23Embedding g • x = y) ↔ triangleType x = triangleType y

theorem construction : CompleteConstruction where
  lattice := leech_constructed
  norm := vector_norm
  finite := finite
  card := card
  factorization := card_factorization
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  cover_injective := embedding_injective
  quotient_injective := toConway1_injective
  quotient_compatible := antipodalStabilizerEquiv_compatible
  shell_card := shell_card
  shell_transitive := shell_transitive
  shell_index := shell_index_product
  line_index := line_index_product
  complement_rank := complement_rank
  complement_free := complement_free
  complement_finite := complement_finite
  integral_faithful := integralRepresentation_injective
  integral_isometric := integralRepresentation_preserves
  degree := degree
  faithful := faithful
  doubly_transitive := two_transitive
  primitive := primitive
  point_heptad_equivariant := pointHeptad_equivariant
  point_stabilizer_order := point_stabilizer_card
  point_stabilizer_transitive := point_stabilizer_complement_transitive
  mathieu_injective := mathieu23Embedding_injective
  mathieu_full := mathieu23Embedding_range
  mathieu_order := triangle_stabilizer_card
  mathieu_maximal := triangle_stabilizer_maximal
  triangle_degree := triangles_card
  triangle_transitive := triangles_transitive
  triangle_primitive := triangles_primitive
  triangle_full_stabilizer := triangle_stabilizer_eq
  triangle_subdegrees := triangle_subdegree
  triangle_orbits := triangle_mathieu_orbits

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.Conway3
