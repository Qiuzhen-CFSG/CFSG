/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Janko2Structure.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Sporadic.Janko2
public import Theory.AtlasPort.Janko2.Conway.IcosianQuaternionicProjectiveAction
public import Theory.AtlasPort.Janko2.Conway.IcosianAngleSuborbits
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionOrders
public import Theory.AtlasPort.Janko2.Conway.IcosianIntegralScalarCompatibility
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisDirectSum

/-!
# Janko2Structure

The concrete Hall–Janko model retains its integral lattice, quaternionic representation,
315 root points, 525 frames, reflection generation, and six angle suborbits.
The wrappers collect the lattice comparisons and geometric results for the same carrier.

Source: Gerald Höhn, `Atlas/Sporadic/Janko2Structure.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Janko2
open Atlas.Algebra Atlas.Lattices Atlas.Conway MulAction
open Atlas.Codes
open scoped DirectSum

abbrev Scalar := icosianOrder
abbrev ScalarField := GoldenRational
abbrev QuaternionAlgebra := IcosianQuaternion
abbrev Coordinates := IcosianRationalCoordinates
abbrev QuaternionicPlane := IcosianQuaternionPoint
abbrev FrameStabilizer := icosianCoordinateFrameStabilizer

def basePoint : Points := icosianRootAxisPoint 0

def baseFrame : Frames := icosianLocalCoordinateRootFrame

def latticeComparison : Coordinates ≃ₗ[ℚ] RationalCoordinates := icosianComparison

def integralComparison : Lattice ≃ₗ[ℤ] leech := icosianLeechEquiv

def integralRightScalars : Scalarᵐᵒᵖ →+* Module.End ℤ leech := icosianLeechRightScalars

def glueComparison : (Lattice ⧸ icosianLatticeTwice) ≃ₗ[Scalarᵐᵒᵖ]
    icosianMatrixGlue GoldenFour := icosianLatticeGlueQuotient

def axisDirectSumComparison : (Π i : Fin 3,icosianLatticeAxis i) ≃ₗ[Scalarᵐᵒᵖ]
    icosianTwiceCoordinates := icosianAxisDirectSumEquiv

def axisExternalDirectSumComparison : (⨁ i : Fin 3,icosianLatticeAxis i) ≃ₗ[Scalarᵐᵒᵖ]
    icosianTwiceCoordinates := icosianAxisExternalDirectSumEquiv

theorem integralRightScalars_injective : Function.Injective integralRightScalars :=
  icosianLeechRightScalars_injective

theorem integralRightScalars_comparison (a : Scalarᵐᵒᵖ) (x : Lattice) :
    integralRightScalars a (integralComparison x) =
      integralComparison (icosianIntegralRightScalars a x) :=
  icosianLeechRightScalars_comparison a x

theorem integralRightScalars_unit (u : RightScalarUnits) (x : leech) :
    integralRightScalars (MulOpposite.op (icosianNormOneToOrder (u⁻¹))) x =
      (rightScalarEmbedding u).val x := icosianLeechRightScalars_unit u x

theorem glue_comparison_reduction (x : Lattice) :
    (glueComparison (Submodule.Quotient.mk x)).val =
      fun i => icosianModuloTwo (x.val i) := icosianLatticeGlueQuotient_mk x

theorem glue_quotient_card : Nat.card (Lattice ⧸ icosianLatticeTwice) = 4096 :=
  icosianLatticeGlueQuotient_card

theorem lattice_axes_sum : (⨆ i : Fin 3,icosianLatticeAxis i) = icosianTwiceCoordinates :=
  icosianLatticeAxes_iSup

def hermitianForm : Coordinates → Coordinates → QuaternionAlgebra := icosianHermitian

def linearRepresentation : LinearCover →* (Coordinates ≃ₗ[ℚ] Coordinates) :=
  icosianHermitianGroup.subtype

def projectiveRepresentation : Model →* Equiv.Perm QuaternionicPlane :=
  icosianQuaternionicProjectiveHom

def reflection : Points → Model := icosianProjectiveReflection

def orthogonal : Points → Points → Prop := IcosianRootPointOrthogonal

def incident (p : Points) (F : Frames) : Prop := p ∈ F.val

def angle : Points → Points → ScalarField := icosianRootPointAngle

def angleValue : Fin 6 → ScalarField := icosianRootPointAngleValues

def subdegree : Fin 6 → ℕ := icosianRootSubdegree

def suborbit (i : Fin 6) : Set Points := {p | icosianRootSuborbitLabel p=i}

theorem lattice_comparison_onto (z : Coordinates) :
    z ∈ rationalIcosianLattice ↔ latticeComparison z ∈ rationalLeech :=
  icosianComparison_lattice_iff z

theorem lattice_comparison_isometry (z w : Coordinates) :
    rationalForm (latticeComparison z) (latticeComparison w) = icosianBilinear z w :=
  icosianComparison_isometry z w

theorem integral_rank : Module.finrank ℤ Lattice = 24 := icosianLeech_rank

theorem integral_free : Module.Free ℤ Lattice := inferInstance

theorem integral_finite : Module.Finite ℤ Lattice := inferInstance

theorem right_scalar_closed (a : Scalarᵐᵒᵖ) (x : IcosianCoordinates)
    (hx : x ∈ icosianLeechModule) : a • x ∈ icosianLeechModule :=
  icosianLeechModule.smul_mem a hx

/-- The right quaternionic coordinate space, expressed over the opposite division ring. -/
def quaternionCoordinateComparison : Coordinates ≃ₗ[QuaternionAlgebraᵐᵒᵖ]
    (Fin 3 → QuaternionAlgebraᵐᵒᵖ) where
  toFun x i := MulOpposite.op (x i)
  invFun x i := MulOpposite.unop (x i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quaternionic_rank : Module.finrank QuaternionAlgebraᵐᵒᵖ Coordinates = 3 := by
  rw [quaternionCoordinateComparison.finrank_eq]
  simp

theorem golden_rank : Module.finrank ScalarField Coordinates = 12 := by
  change Module.finrank GoldenRational (Fin 3 → Quaternion GoldenRational) = 12
  simp [Module.finrank_pi_fintype,Quaternion.finrank_eq_four]

theorem rational_rank : Module.finrank ℚ Coordinates = 24 := by
  rw [icosianRealCoordinates.finrank_eq]
  simp [IcosianRealIndex]

theorem full_centralizer : embedding.range = icosianCentralizer :=
  icosianHermitianToCo0_range

theorem linear_faithful : Function.Injective linearRepresentation := Subtype.val_injective

theorem linear_right_linear (g : LinearCover) (a : QuaternionAlgebra) (z : Coordinates) :
    linearRepresentation g (icosianRightMul z a) =
      icosianRightMul (linearRepresentation g z) a := g.property.1 a z

theorem linear_hermitian (g : LinearCover) (z w : Coordinates) :
    hermitianForm (linearRepresentation g z) (linearRepresentation g w) = hermitianForm z w :=
  g.property.2.1 z w

theorem linear_lattice (g : LinearCover) (z : Coordinates) :
    z ∈ rationalIcosianLattice ↔ linearRepresentation g z ∈ rationalIcosianLattice :=
  g.property.2.2 z

theorem degree : Nat.card Points = 315 := icosianRootPoint_card

theorem faithful : FaithfulSMul Model Points := inferInstance

theorem primitive : IsPreprimitive Model Points := icosianProjective_rootPoint_primitive

theorem transitive : IsPretransitive Model Points := inferInstance

theorem quaternionic_projective_faithful : Function.Injective projectiveRepresentation :=
  icosianQuaternionicProjectiveHom_injective

theorem quaternionic_projective_kernel :
    (toPermHom LinearCover QuaternionicPlane).ker = icosianCentralSigns :=
  icosian_quaternionic_projective_kernel

theorem point_kernel : (toPermHom LinearCover Points).ker = icosianCentralSigns :=
  icosian_rootPoint_kernel

theorem frame_count : Nat.card Frames = 525 := icosianRootFrames_card

theorem frame_size (F : Frames) : F.val.card = 3 := F.property.1

theorem frame_orthogonal (F : Frames) (p q : Points)
    (hp : incident p F) (hq : incident q F) (hne : p ≠ q) : orthogonal p q :=
  F.property.2 hp hq hne

theorem frame_transitive : IsPretransitive LinearCover Frames := inferInstance

theorem full_frame_stabilizer : stabilizer LinearCover baseFrame = icosianCoordinateFrameStabilizer :=
  icosianLocalCoordinateRootFrame_stabilizer

theorem frame_stabilizer_card : Nat.card FrameStabilizer = 2304 :=
  icosianCoordinateFrameStabilizer_card

theorem orthogonal_count (p : Points) : Nat.card (IcosianRootNeighbors p) = 10 :=
  icosianRootNeighbors_card p

theorem orthogonal_completion (p q : Points) (hpq : orthogonal p q) :
    ∃! r : Points, orthogonal p r ∧ orthogonal q r := icosianRootPoint_completion p q hpq

theorem reflection_square (p : Points) : reflection p * reflection p = 1 :=
  icosianProjectiveReflection_square p

theorem reflection_order (p : Points) : orderOf (reflection p) = 2 :=
  icosianProjectiveReflection_order p

theorem local_reflection_card (p : Points) : Nat.card (icosianProjectiveLineInvolutions p) = 2 :=
  icosianProjectiveLineInvolutions_card p

theorem local_reflection_central (p : Points) :
    (icosianProjectiveLineInvolutions p).subgroupOf (stabilizer Model p) ≤
      Subgroup.center (stabilizer Model p) := icosianProjectiveLineInvolutions_central p

theorem reflection_conjugate (g : Model) (p : Points) :
    g * reflection p * g⁻¹ = reflection (g • p) :=
  icosianProjectiveReflection_conjugate g p

theorem reflection_generation : Subgroup.closure (Set.range reflection) = ⊤ :=
  icosianProjectiveReflection_generation

theorem full_reflection_generation : icosianReflectionGroup = ⊤ :=
  icosianReflectionGroup_eq_top

theorem angle_invariant (g : Model) (p q : Points) : angle (g • p) (g • q) = angle p q :=
  icosianRootPointAngle_projective_smul g p q

theorem angle_values_injective : Function.Injective angleValue :=
  icosianRootPointAngleValues_injective

theorem angle_exhaustive (p q : Points) : ∃ i : Fin 6, angle p q = angleValue i :=
  icosianRootPointAngle_exhaustive p q

theorem angle_card (p : Points) (i : Fin 6) :
    Nat.card {q : Points // angle p q=angleValue i} = subdegree i :=
  icosianRootPointAngleLevel_card p i

theorem angle_stabilizer_orbit (p q : Points) :
    orbit (stabilizer Model p) q = {r : Points | angle p r = angle p q} :=
  icosianRootPointAngle_projective_stabilizer_orbit p q

theorem suborbit_card (i : Fin 6) : Nat.card (suborbit i) = subdegree i :=
  icosianRootSuborbitLabel_fiber_card i

theorem suborbit_cover (p : Points) : ∃ i : Fin 6, p ∈ suborbit i :=
  ⟨icosianRootSuborbitLabel p,rfl⟩

theorem suborbit_pairwise : Pairwise (fun i j => Disjoint (suborbit i) (suborbit j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  exact hij (hpi.symm.trans hpj)

theorem suborbit_is_orbit (i : Fin 6) (p : Points) (hp : p ∈ suborbit i) :
    orbit (stabilizer Model basePoint) p = suborbit i := by
  rw [icosianProjectiveStabilizer_orbit]
  change orbit icosianFullAxisStabilizer p = _
  rw [icosianFullAxisStabilizer_orbit]
  ext q
  change icosianRootPointNormWord q 0=icosianRootPointNormWord p 0 ↔ _
  rw [(icosianRootSuborbitLabel_eq_iff p i).mp hp]
  exact (icosianRootSuborbitLabel_eq_iff q i).symm

end Atlas.Sporadic.Janko2
