module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy

/-!
# Complete homogeneous models with a prescribed stabilizer

Geometric Borel conjugacy transports the existing complete flag model to any
specified Borel. Conversely, a connected solvable stabilizer of a transitive
regular action on a complete variety is Borel: a Borel subgroup fixes a point,
so it lies in a conjugate of the stabilizer, and maximality gives equality.

This implements the maximality step of Borel, *Linear Algebraic Groups*,
§11.15. Applying the fixed-point theorem directly on the complete orbit
avoids transferring completeness through a quotient bijection.
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Bor1 Variety.Geometric

attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
set_option linter.style.haveILetI false

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

/-- The distinguished point in an actual geometric homogeneous model. -/
@[expose] public noncomputable def modelBasePoint {B : ClosedSubgroup H}
    (M : CompleteModel B) : Point M.variety :=
  M.pointEquiv.symm (borelHomogeneousSpace.basePoint B)

/-- The geometric model has the prescribed stabilizer at its basepoint. -/
public theorem modelBasePoint_stabilizer {B : ClosedSubgroup H}
    (M : CompleteModel B) (g : Variety.Point H) :
    M.action.toMulAction.smul g (modelBasePoint M) = modelBasePoint M ↔
      g ∈ B.toSubgroup := by
  rw [← M.pointEquiv.injective.eq_iff, M.equivariant]
  simp only [modelBasePoint, Equiv.apply_symm_apply]
  have hproj : g • borelHomogeneousSpace.basePoint B =
      borelHomogeneousSpace.projection B g := by
    simpa using (borelHomogeneousSpace.projection_mul B g 1).symm
  rw [hproj, ← borelHomogeneousSpace.projection_one B,
    borelHomogeneousSpace.projection_eq_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    have hg : g = b⁻¹ := eq_inv_of_mul_eq_one_left he.symm
    rw [hg]
    exact B.toSubgroup.inv_mem hb
  · intro hg
    exact ⟨g⁻¹, B.toSubgroup.inv_mem hg, by simp⟩

/-- The action on a complete homogeneous model is transitive from its basepoint. -/
public theorem modelBasePoint_transitive {B : ClosedSubgroup H}
    (M : CompleteModel B) (y : Point M.variety) :
    ∃ g : Variety.Point H, M.action.toMulAction.smul g (modelBasePoint M) = y := by
  obtain ⟨g, hg⟩ := borelHomogeneousSpace.projection_surjective B (M.pointEquiv y)
  refine ⟨g, M.pointEquiv.injective ?_⟩
  rw [M.equivariant]
  simp only [modelBasePoint, Equiv.apply_symm_apply]
  have he := borelHomogeneousSpace.projection_mul B g 1
  simpa only [mul_one, borelHomogeneousSpace.projection_one] using he.symm.trans (by simpa using hg)

/-- Every specified Borel has a genuine complete geometric homogeneous model. -/
public theorem nonempty_completeModel (B : ClosedSubgroup H) (hB : IsBorelSubgroup B) :
    Nonempty (CompleteModel B) := by
  obtain ⟨D, hD, ⟨M⟩⟩ := exists_borel_completeModel B hB
  obtain ⟨g, hg⟩ := BorelGeometricConjugacy.conjugacy hD hB
  letI := M.action.toMulAction
  let x := g • modelBasePoint M
  have htrans (y : Point M.variety) : ∃ a : Variety.Point H, a • x = y := by
    obtain ⟨a, ha⟩ := modelBasePoint_transitive M y
    change a • modelBasePoint M = y at ha
    refine ⟨a * g⁻¹, ?_⟩
    simpa only [x, smul_smul, inv_mul_cancel_right] using ha
  have hstab (a : Variety.Point H) : a • x = x ↔ a ∈ B.toSubgroup := by
    rw [hg]
    change a • x = x ↔ a ∈ D.conjugate g
    rw [D.mem_conjugate_iff]
    rw [← modelBasePoint_stabilizer M]
    change a • (g • modelBasePoint M) = g • modelBasePoint M ↔
      (g⁻¹ * a * g) • modelBasePoint M = modelBasePoint M
    constructor
    · intro he
      simpa only [smul_smul, mul_assoc, inv_mul_cancel, one_smul] using congrArg (g⁻¹ • ·) he
    · intro he
      have hh := congrArg (g • ·) he
      simpa only [smul_smul, mul_assoc, mul_inv_cancel_left] using hh
  exact ⟨CompleteModel.ofTransitive B M.action x M.complete htrans hstab⟩

omit [IsAlgClosed k] in
private theorem carrier_connected (K : ClosedSubgroup H)
    (hK : _root_.IsConnected (K : Set (Variety.Point H))) :
    Variety.IsConnected K.carrierVariety := by
  let : ConnectedSpace {x : Variety.Point H // x ∈ (K : Set (Variety.Point H))} :=
    Subtype.connectedSpace hK
  let : ConnectedSpace (Variety.Point K.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph K.isZariskiClosed).connectedSpace_iff.mpr
      inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- A connected solvable subgroup with a complete homogeneous model is Borel.
This uses the actual regular action and genuine geometric completeness. -/
public theorem isBorel_of_completeModel (K : ClosedSubgroup H)
    (hKc : _root_.IsConnected (K : Set (Variety.Point H)))
    (hKs : Group.IsSolvable (Variety.Point K.carrierVariety))
    (M : CompleteModel K) : IsBorelSubgroup K := by
  obtain ⟨D, hD, -⟩ := exists_borelSubgroup_containing_connected_solvable K hKc hKs
  obtain ⟨x, hx⟩ := M.homogeneousSpace_fixed_of_isBorel hD
  obtain ⟨g, hg⟩ := subgroup_le_conjugate_of_homogeneousSpace_fixed K D.toSubgroup x hx
  have hgc : _root_.IsConnected (K.conjugate g : Set (Variety.Point H)) := by
    have hc := (algebraicGroupIso_isConnected_iff (K.conjugateIso g)).mp
      (carrier_connected K hKc)
    let : ConnectedSpace (Variety.Point (K.conjugate g).carrierVariety) :=
      connectedSpace_iff_univ.mpr hc
    change _root_.IsConnected ((K.conjugate g).toSubgroup : Set (Variety.Point H))
    rw [← (K.conjugate g).range_inclusion]
    exact isConnected_range (K.conjugate g).inclusion.toVariety.continuous
  have hgs : Group.IsSolvable (Variety.Point (K.conjugate g).carrierVariety) := by
    let : Group.IsSolvable (Variety.Point K.carrierVariety) := hKs
    exact Group.isSolvable_of_surjective (f := (K.conjugateIso g).hom.onPoints)
      (K.conjugateIso g).toMulEquiv.surjective
  have heq := hD.maximal (K.conjugate g) hgc hgs hg
  have hback := hD.conjugate g⁻¹
  rw [← heq, ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
    ClosedSubgroup.conjugate_one] at hback
  exact hback

/-- A connected solvable point stabilizer on a complete transitive variety is Borel. -/
public theorem isBorel_of_complete_transitive_action (K : ClosedSubgroup H)
    (hKc : _root_.IsConnected (K : Set (Variety.Point H)))
    (hKs : Group.IsSolvable (Variety.Point K.carrierVariety))
    {X : Variety.Geometric k} (A : MorphicAction H X) (x : Point X)
    (hX : IsComplete X)
    (htrans : ∀ y : Point X, ∃ g : Variety.Point H, A.toMulAction.smul g x = y)
    (hstab : ∀ g : Variety.Point H, A.toMulAction.smul g x = x ↔ g ∈ K.toSubgroup) :
    IsBorelSubgroup K :=
  isBorel_of_completeModel K hKc hKs (CompleteModel.ofTransitive K A x hX htrans hstab)

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
