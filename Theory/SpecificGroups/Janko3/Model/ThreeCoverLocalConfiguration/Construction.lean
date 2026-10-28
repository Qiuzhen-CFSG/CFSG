module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Plane
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.RightSupport

/-!
# Assembly of the marked J₃ affine three-cover configuration

The concrete plane, its injectivity, its normalization of a nontrivial
translation two-subgroup, and its centralization of the right support are
proved by the imported certificates. Commutator identities prove perfectness
of the left support, and power relations in the abelianization prove perfectness
of the right support. Their certified orders, 1920 and 60, give cyclic Sylow
three-subgroups; checked words place the marked cubic elements in these supports.

`configuration` discharges all six inputs of the preserved conditional assembly
`configurationOfSupports`, giving a concrete inhabitant on the actual
degree-6156 model without extra hypotheses. This supplies the configuration
premise of `Sporadic.Janko3.exists_local_e9_lift_of_configuration`; the central
cover assembly remains in its consumer.

Sources: GLS, Number 3, Table 5.3h, printed p.269; Aschbacher--Smith A.2.19,
printed p.41, and I.2.1, printed p.409.
-/

namespace Sporadic.Janko3.ThreeCoverConfig

/-- Assemble all the checked plane and translation facts with the two concrete
support certificates. No covering or rank conclusion is an input. -/
public def configurationOfSupports
    (hC : Group.IsPerfect leftSupport) (hD : Group.IsPerfect rightSupport)
    (sC : ∀ S : Sylow 3 leftSupport, IsCyclic S)
    (sD : ∀ S : Sylow 3 rightSupport, IsCyclic S)
    (hx : x ∈ leftSupport) (hy : y ∈ rightSupport) : ThreeCoverLocalConfiguration where
  twoSubgroup := twoSubgroup
  two_nontrivial := two_nontrivial
  two_isPGroup := two_isPGroup
  leftSupport := leftSupport
  rightSupport := rightSupport
  left_perfect := hC
  right_perfect := hD
  left_cyclicSylow := sC
  right_cyclicSylow := sD
  plane := plane
  plane_injective := plane_injective
  left_mem := plane_left_mem hx
  right_mem := plane_right_mem hy
  left_centralizes := plane_left_centralizes
  normalizes := plane_normalizes

/-- The certified affine configuration on the actual degree-6156 J₃ model. -/
public def configuration : ThreeCoverLocalConfiguration :=
  configurationOfSupports leftSupport_perfect right_perfect
    leftSupport_cyclicSylow right_cyclicSylow x_mem_leftSupport y_mem_right

/-- All downstairs premises of the central three-cover lifting argument hold
in the concrete J₃ model. -/
public theorem configuration_nonempty : Nonempty ThreeCoverLocalConfiguration :=
  ⟨configuration⟩

end Sporadic.Janko3.ThreeCoverConfig
