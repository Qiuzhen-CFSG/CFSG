module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Geometry
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Kernel
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Frame
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.OrbitAction

/-!
# Constructing a double cover of the actual Rudvalis permutation model

The concrete group of matrix/permutation pairs is finite and perfect and maps
surjectively onto `Rudvalis.Model`. Its first generator squares to a nonidentity
kernel involution. The checked orbit action and projective frame make the kernel
scalar. Its order is then two or four, and quotienting the order-four case by
the displayed involution constructs a perfect central cover with kernel two.

`doubleCover` discharges both geometric premises on the literal published
tables. `Carrier`, `covering`, and `kernel_card_two` expose the resulting finite
perfect central double cover of the original degree-4060 `Rudvalis.Model`.
The conditional constructor `doubleCoverOfGeometry` is retained. Universality
is neither used nor asserted; the independent multiplier upper bound belongs
to `Multiplier.lean`.

Source: Aschbacher–Smith I.1.3(1), printed p.407; ATLAS `2RuG1-f5r28B0`.
-/

namespace Rudvalis.Multiplier.DoubleCover

/-- Actual covering construction, conditional on the two finite geometry checks. -/
public noncomputable def doubleCoverOfGeometry
    (horbit : OrbitEquivariance) (hframe : FrameRigidity) : FiniteDoubleCover :=
  doubleCoverOfScalarKernel (scalarKernel_of_geometry horbit hframe)

/-- The actual projection kernel consists of scalar matrices. -/
public theorem scalarKernel : ScalarKernel :=
  scalarKernel_of_geometry orbitEquivariance frameRigidity

/-- The finite perfect central double cover, with both geometry checks discharged. -/
public noncomputable def doubleCover : FiniteDoubleCover :=
  doubleCoverOfGeometry orbitEquivariance frameRigidity

/-- The concrete paired group, or its quotient by the displayed central involution. -/
public abbrev Carrier : Type := doubleCover.Carrier

public noncomputable instance carrier_group : Group Carrier := doubleCover.group

public instance carrier_finite : Finite Carrier := doubleCover.finite

/-- The constructed covering has the original permutation model as literal codomain. -/
public noncomputable def covering : PerfectCentralCovering.Cover Carrier Rudvalis.Model :=
  doubleCover.covering

public instance carrier_isPerfect : Group.IsPerfect Carrier := covering.isPerfect

public theorem covering_surjective : Function.Surjective covering.toMonoidHom :=
  covering.surjective

public theorem covering_ker_le_center :
    covering.toMonoidHom.ker ≤ Subgroup.center Carrier :=
  covering.ker_le_center

/-- The constructed cover has kernel of exactly order two, without an upper-bound premise. -/
public theorem kernel_card_two : Nat.card covering.toMonoidHom.ker = 2 :=
  doubleCover.kernel_card_two

end Rudvalis.Multiplier.DoubleCover
