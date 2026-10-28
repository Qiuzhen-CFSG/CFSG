module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The marked quaternion-kernel centralizer in M₁₂

The first parabolic of the checked M₁₂ small pair is the full centralizer
of its marked involution. Its normal core is the embedded Q₈ * Q₈, and the
quotient is the permutation action on three matchings. Transporting the two
quaternion factors to the actual normal kernel gives S₃/Q₈² with no splitting
assumption.

This proves the marked central class in Aschbacher–Smith 16.1.5(4), printed
p.1171. Coverage of the other inner class and the outer classes is separate.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

/-- The marked conjugation automorphism is an involution, not the identity. -/
theorem m12_marked_inner_order : orderOf (MulAut.conj z) = 2 :=
  (orderOf_injective MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot m12_center_eq_bot) z).trans z_order

/-- The exact kernel and quotient of the marked M₁₂ involution centralizer. -/
theorem m12_marked_centralizer_quaternion_extension :
    IsM12QuaternionExtension (centralizer ({z} : Set M12)) := by
  change IsM12QuaternionExtension firstParabolic
  refine ⟨core.subgroupOf firstParabolic, inferInstance, ?_, ⟨firstParabolicCoreQuotient⟩⟩
  exact ⟨coreQuaternionData.map (subgroupOfEquivOfLe core_le_firstParabolic).symm⟩

/-- The corresponding fixed subgroup of the actual inner automorphism. -/
theorem m12_marked_inner_alternative : M12InvolutionAlternative (MulAut.conj z) := by
  refine Or.inl ⟨⟨z, rfl⟩, Or.inl ?_⟩
  rw [MulAut.fixedSubgroup_conj]
  exact m12_marked_centralizer_quaternion_extension

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
