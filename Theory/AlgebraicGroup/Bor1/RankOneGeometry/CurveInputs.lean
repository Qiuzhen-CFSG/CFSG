module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.OrbitDimension
public import Theory.AlgebraicGroup.Variety.GeometricDimension
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Tori.Power
public import Theory.AlgebraicGroup.Borel.Defs
/-!
# Source inputs for the semisimple rank-one Borel curve

The maximal torus acts nontrivially on the Borel orbit. Otherwise it lies in
the normal core of the Borel. The closure of that core is solvable and normal;
its identity component contains the connected torus and lies in the radical,
contradicting semisimplicity and the torus's positive dimension.

An irreducible zero-dimensional variety has at most one rational point.
Consequently the actual projective Borel orbit, already known to have dimension
at most one, has dimension exactly one. The final source theorem constructs
all Chevalley representation data and the nontrivial torus-action witness.
These are the original inputs to Borel, *Linear Algebraic Groups*, §13.13(3–4),
with no rationality, projective-line, or separability assumption.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X : Type v} [MulAction (Variety.Point G) X]

theorem exists_torus_moved_borel_orbit_point
    (hG : IsSemisimpleAlgebraicGroup G) (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) (x : X)
    (hstab : ∀ a : Variety.Point G,a • x=x ↔ a∈B.toSubgroup) :
    ∃ (t : Variety.Point G),t∈T.toSubgroup ∧ ∃ g : Variety.Point G,t • (g • x) ≠ g • x := by
  classical
  by_contra! hfix
  let K := subgroupZariskiClosure G B.toSubgroup.normalCore
  have hKnormal : K.toSubgroup.Normal :=
    subgroupZariskiClosure_isNormal G _ inferInstance
  have hKB : K ≤ B :=
    closure_minimal B.toSubgroup.normalCore_le
      (Variety.isClosed_iff_isZariskiClosed.mpr B.isZariskiClosed)
  have hTK : T ≤ K := by
    intro t ht
    apply subset_closure
    change ∀ a : Variety.Point G,a*t*a⁻¹ ∈ B.toSubgroup
    intro a
    apply (hstab _).mp
    simp only [mul_smul,hfix t ht a⁻¹,smul_inv_smul]
  have hTc : _root_.IsConnected (T : Set (Variety.Point G)) := by
    letI : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [←T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  let N := K.identityComponentAmbient
  have hTN : T ≤ N := connected_closedSubgroup_le_identityComponentAmbient T K hTc hTK
  have hNB : N ≤ B := fun n hn => hKB (K.identityComponentAmbient_le hn)
  have hNsol : Group.IsSolvable (Variety.Point N.carrierVariety) := by
    let eB : Variety.Point B.carrierVariety ≃* B.toSubgroup := Equiv.mulEquiv B.pointEquiv
    let eN : Variety.Point N.carrierVariety ≃* N.toSubgroup := Equiv.mulEquiv N.pointEquiv
    let f := eB.symm.toMonoidHom.comp ((Subgroup.inclusion hNB).comp eN.toMonoidHom)
    letI := hB.solvable
    exact Group.isSolvable_of_isSolvable_injective (f := f)
      (eB.symm.injective.comp ((Subgroup.inclusion_injective hNB).comp eN.injective))
  obtain ⟨R,hR⟩ := exists_radical G
  have hNR : N ≤ R := hR.maximal N
    (K.identityComponentAmbient_normal_of_normal hKnormal)
    K.identityComponentAmbient_isConnected hNsol
  have hTbot : T.toSubgroup ≤ ⊥ := by
    rw [←hG.2 R hR]
    exact fun t ht => hNR (hTN ht)
  letI : Subsingleton T.toSubgroup := ⟨fun x y => Subtype.ext
    ((Subgroup.mem_bot.mp (hTbot x.2)).trans (Subgroup.mem_bot.mp (hTbot y.2)).symm)⟩
  letI : Subsingleton (Variety.Point T.carrierVariety) := T.pointEquiv.subsingleton
  have hzero := (dimension_zero_iff_finite_points T.carrierVariety).mpr inferInstance
  rw [hdimT] at hzero
  norm_num at hzero
end Theory.AlgebraicGroup.Bor1.RankOneGeometry

open AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem subsingleton_points_of_irreducible_dimension_le_zero
    (X : Geometric k) [IrreducibleSpace X.toScheme] (hdim : dimension X ≤ 0) :
    Subsingleton (Point X) := by
  constructor
  intro p q
  let z := pointEquivClosedPoint X.structureMap p
  let Z : IrreducibleCloseds X.toScheme := ⟨{z.1},isIrreducible_singleton,z.2⟩
  let W : IrreducibleCloseds X.toScheme :=
    ⟨Set.univ,IrreducibleSpace.isIrreducible_univ _,isClosed_univ⟩
  have hZW : Z ≤ W := Set.subset_univ _
  have hWZ : W ≤ Z := (Order.krullDim_nonpos_iff_forall_isMax.mp hdim) Z hZW
  have he : (pointEquivClosedPoint X.structureMap q).1 = z.1 :=
    hWZ (Set.mem_univ _)
  apply (pointEquivClosedPoint X.structureMap).injective
  exact Subtype.ext he.symm
end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
open Variety.Geometric AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]

theorem projective_borel_orbit_dimension_eq_one
    (hG : IsSemisimpleAlgebraicGroup G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E))
    (he : ∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
      projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x=x ↔ g∈B.toSubgroup) :
    dimension (A.orbitSubvariety x).toGeometric = 1 := by
  apply le_antisymm (projective_borel_orbit_dimension_le_one hG.1 T hT hdimT B hB ρ hρ b A x he hstab)
  have hclosed := A.orbit_isClosed_of_borel_fixed hG.1 B hB x (fun g hg => (hstab g).mpr hg)
  let O := A.orbitSubvariety x
  letI : IsClosedImmersion O.inclusion.hom := A.orbitSubvariety_isClosedImmersion x hclosed
  letI : IrreducibleSpace O.toGeometric.toScheme := A.orbitSubvariety_isIrreducible_of_isClosed hG.1 x hclosed
  letI := A.toMulAction
  obtain ⟨t,ht,g,hmove⟩ := exists_torus_moved_borel_orbit_point hG T hT.1 hdimT B hB x hstab
  have hlift (a : Variety.Point G) : ∃ y : Point O.toGeometric,O.inclusion y=a • x := by
    apply (O.inclusion.point_mem_range_iff_closedPoint_mem_range (a • x)).mpr
    rw [A.orbitSubvariety_range]
    exact (A.point_mem_orbit_range_iff x _).mpr ⟨a,rfl⟩
  obtain ⟨y,hy⟩ := hlift g
  obtain ⟨z,hz⟩ := hlift (t*g)
  have hpos : 0 < dimension O.toGeometric := by
    apply lt_of_not_ge
    intro hzero
    letI := subsingleton_points_of_irreducible_dimension_le_zero O.toGeometric hzero
    have hh := congrArg (fun y => O.inclusion y) (Subsingleton.elim z y)
    rw [hz,hy,mul_smul] at hh
    exact hmove hh
  simpa only [Nat.cast_zero,zero_add] using (ENat.WithBot.add_one_le_iff (n := 0)).mpr hpos

/-- The literal semisimple rank-one source supplies the actual projective curve,
its dimension, and a nontrivial action of the original maximal torus. -/
theorem exists_projective_rank_one_curve_inputs
    (hG : IsSemisimpleAlgebraicGroup G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (ρ : RationalRepresentation G E)
      (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E)),
      IsRationalRepresentation ρ ∧
      (∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
        projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
        Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b p)) ∧
      (∀ g : Variety.Point G,A.toMulAction.smul g x=x ↔ g∈B.toSubgroup) ∧
      dimension (A.orbitSubvariety x).toGeometric = 1 ∧
      ∃ (t : Variety.Point T.carrierVariety) (g : Variety.Point G),
        A.toMulAction.smul (T.includePoint t) (A.toMulAction.smul g x) ≠
          A.toMulAction.smul g x := by
  obtain ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hstab⟩ :=
    TorusBorelGeneration.exists_projective_action_stabilizer B
  refine ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hstab,
    projective_borel_orbit_dimension_eq_one hG T hT hdimT B hB ρ hρ b A x he hstab,?_⟩
  letI := A.toMulAction
  obtain ⟨t,ht,g,hmove⟩ := exists_torus_moved_borel_orbit_point hG T hT.1 hdimT B hB x hstab
  refine ⟨T.pointEquiv.symm ⟨t,ht⟩,g,?_⟩
  change A.toMulAction.smul t (A.toMulAction.smul g x) ≠ A.toMulAction.smul g x at hmove
  simpa only [ClosedSubgroup.includePoint,Equiv.apply_symm_apply] using hmove
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
