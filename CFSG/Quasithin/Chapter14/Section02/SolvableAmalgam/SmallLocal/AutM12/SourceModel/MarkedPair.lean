module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.MarkedMovement

/-!
# The compatible marked Aut(M₁₂) pair

The verified degree-24 pair supplies all of `CompatibleMarkedPair`: the whole
common Sylow subgroup, the marked center, the original two quaternion factors,
and the natural four as the literal conjugate-generated subgroup. The basis
changes in the two quaternion factors come from the checked movement maps.
The four second-parabolic equations are inherited from their concrete proof.

The order-64 movement subgroup is proved different from the actual first
two-core. This witness supplies the local pair; it does not construct the
additional binary-tetrahedral embeddings in a larger ambient residual.
Source: Aschbacher--Smith, proof of 14.2.21, printed p.988, refs/quasithin.pdf.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel
open Sporadic.Mathieu.M12ExceptionalExtension
open FirstParabolic
open SourceCoreAction.MarkedMovement
attribute [local irreducible] z

theorem distinguished_movement : distinguished = QuaternionSwapModel.Z.map SecondCoordinates.movement := by
  ext x
  constructor
  · intro hx
    rcases (mem_distinguished x).mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨QuaternionSwapModel.z, (QuaternionSwapModel.mem_Z _).mpr (Or.inr rfl),
        SecondCoordinates.movement_z⟩
  · rintro ⟨q,hq,rfl⟩
    rcases (QuaternionSwapModel.mem_Z q).mp hq with rfl | rfl
    · simpa only [map_one] using distinguished.one_mem
    · rw [SecondCoordinates.movement_z]
      exact Subgroup.mem_zpowers _

theorem distinguished_normal_overlap : (distinguished.subgroupOf overlap).Normal := by
  constructor
  intro x hx g
  change (g : Carrier) * (x : Carrier) * (g : Carrier)⁻¹ ∈ distinguished
  rcases (mem_distinguished x.val).mp hx with h | h
  · rw [h, mul_one, mul_inv_cancel]
    exact distinguished.one_mem
  · rw [h, SecondCoordinates.overlap_conjugates_z]
    exact Subgroup.mem_zpowers _

theorem natural_conjugateClosure : natural = Subgroup.closure
    {w : Carrier | ∃ a ∈ secondParabolic, ∃ x ∈ distinguished, a * x * a⁻¹ = w} := by
  rw [distinguished_movement,
    VerifiedPair.secondGeometry.conjugateClosure_eq_plane,
    SecondCoordinates.movement_plane]

theorem leftFactor_movement : leftFactor =
    QuaternionSwapModel.leftFactor.map SecondCoordinates.movement := by
  rw [SecondCoordinates.movement_leftFactor innerModel]
  unfold leftFactor Sporadic.Mathieu.M12SmallPair.leftFactor
  rw [← MonoidHom.range_comp]
  congr 1
  apply MonoidHom.ext
  intro q
  exact (map_leftLift innerModel q).symm

theorem rightFactor_movement : rightFactor =
    QuaternionSwapModel.rightFactor.map SecondCoordinates.movement := by
  rw [SecondCoordinates.movement_rightFactor innerModel]
  unfold rightFactor Sporadic.Mathieu.M12SmallPair.rightFactor
  rw [← MonoidHom.range_comp]
  congr 1
  apply MonoidHom.ext
  intro q
  exact (map_rightLift innerModel q).symm

/-- All local-pair equations use the concrete whole overlap and original quaternion factors. -/
def compatibleMarkedPair : CompatibleMarkedPair SecondCoordinates.movement
    VerifiedPair.commonSylow firstParabolic secondParabolic distinguished natural
    quaternionCore leftFactor rightFactor where
  toSecondGeometry := VerifiedPair.secondGeometry
  whole_overlap := rfl
  marked := distinguished_movement
  marked_normal := distinguished_normal_overlap
  core := by
    rw [VerifiedPair.movement_residual_image, mapped_pCore_residual_commutator innerModel]
  left_factor := leftFactor_movement
  right_factor := rightFactor_movement
  natural := natural_conjugateClosure

/-- The movement embedding is distinct from the actual first two-core. -/
theorem movement_range_ne_twoCore : SecondCoordinates.movement.range ≠
    (pCore 2 firstParabolic).map firstParabolic.subtype := by
  intro h
  rw [mapped_pCore_eq_outerCore innerModel] at h
  let e : QuaternionSwapModel.QH ≃* outerCore :=
    (MonoidHom.ofInjective SecondCoordinates.movement_injective).trans (MulEquiv.subgroupCongr h)
  exact outerCore_not_equiv_split innerModel ⟨e.symm⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel
