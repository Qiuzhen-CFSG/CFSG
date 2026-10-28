module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of a binary plane stabilizer in dimension four

Restriction to a plane and passage to the quotient give the two actual
diagonal actions. Their kernel is elementary abelian, and each binary
two-dimensional linear group is S₃. Thus a faithful action preserving a
plane with plane quotient has solvable acting group.

Source application: Aschbacher--Smith G.10.5, printed p.359.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace BinaryLinear.SmallParabolicLevi
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual automorphism group of a binary plane is solvable. -/
theorem linearGroup_solvable_of_finrank_two (hd : finrank (ZMod 2) V = 2) :
    Group.IsSolvable (BinaryLinear.GL V) := by
  classical
  let e : V ≃ₗ[ZMod 2] OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let : Group.IsSolvable (alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((linearGroupCongr e).trans linearTwoEquivSymmetricThree).toMonoidHom)
    ((linearGroupCongr e).trans linearTwoEquivSymmetricThree).injective

/-- The literal 2+2 parabolic is an elementary abelian extension of solvable groups. -/
theorem parabolic_solvable_of_plane_and_quotient_plane (W : Submodule (ZMod 2) V)
    (hW : finrank (ZMod 2) W = 2) (hq : finrank (ZMod 2) (V ⧸ W) = 2) :
    Group.IsSolvable (parabolic W) := by
  let : Group.IsSolvable (BinaryLinear.GL W) := linearGroup_solvable_of_finrank_two hW
  let : Group.IsSolvable (BinaryLinear.GL (V ⧸ W)) := linearGroup_solvable_of_finrank_two hq
  let f := blockAction W
  have hker : IsElementaryAbelian 2 f.ker := by
    apply BinaryTransvectionGroups.elementaryAbelian_of_le_radical
      ((parabolic W).subtype.comp f.ker.subtype)
      (Subtype.val_injective.comp Subtype.val_injective) W
    intro k
    exact (ker_blockAction W).le k.property
  let : Group.IsSolvable f.ker :=
    Group.isSolvable_of_comm hker.toIsMulCommutative.is_comm.comm
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

end BinaryLinear.SmallParabolicLevi

namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful binary representation preserving two plane factors has solvable actor. -/
theorem isSolvable_of_faithful_plane_and_quotient_plane
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (U : Subrepresentation ρ) (hU : finrank (ZMod 2) U.toSubmodule = 2)
    (hq : finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2) : Group.IsSolvable G := by
  let a : G →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have ha (g : G) : a g ∈ BinaryLinear.parabolic U.toSubmodule := by
    intro w
    change ρ g w ∈ U.toSubmodule ↔ w ∈ U.toSubmodule
    constructor
    · intro hw
      have he := U.apply_mem_toSubmodule g⁻¹ hw
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using he
    · exact fun hw => U.apply_mem_toSubmodule g hw
  let f := a.codRestrict (BinaryLinear.parabolic U.toSubmodule) ha
  have hfi : Function.Injective f := by
    intro g k h
    apply hf
    apply LinearMap.ext
    intro w
    exact congrArg (fun e : BinaryLinear.parabolic U.toSubmodule => e.val w) h
  let : Group.IsSolvable (BinaryLinear.parabolic U.toSubmodule) :=
    BinaryLinear.SmallParabolicLevi.parabolic_solvable_of_plane_and_quotient_plane _ hU hq
  exact Group.isSolvable_of_isSolvable_injective hfi

end Representation
