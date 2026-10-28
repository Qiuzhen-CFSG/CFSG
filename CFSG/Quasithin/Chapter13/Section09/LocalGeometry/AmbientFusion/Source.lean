module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion.Pair
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Closure

/-!
# Original-input applications of the ambient fusion branch

The constructed marked pair discharges every earlier pair and four-group
premise in the actual centralizer consumers. In the original S4 wreath C2
configuration, condition (E) alone now gives Q normal in C_G(z) and C_G(z)
solvable; all coordinate inclusions and the central quotient remain literal.

Source: Aschbacher–Smith 13.9.2, 13.9.7, and the normality and solvability
steps in 13.9.8, printed pp.969–972.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup CentralizerStructure
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

theorem exists_marked_pairData :
    ∃ p : PairData d, p.t = m.t ∧ p.z = m.z :=
  ⟨m.pairData,rfl,rfl⟩

theorem pairData_closure : m.pairData.ClosureData :=
  m.closureData m.pairData rfl rfl

theorem marked_core_normal (hE : IsEvenCharacteristicAt d.T) :
    (m.core.subgroupOf (centralizer ({m.z} : Set G))).Normal :=
  m.core_normal_of_pair m.pairData rfl rfl hE

theorem marked_centralizer_z_solvable (hE : IsEvenCharacteristicAt d.T) :
    Group.IsSolvable (centralizer ({m.z} : Set G)) :=
  m.centralizer_z_solvable_of_pair m.pairData rfl rfl hE

end CFSG.Quasithin.Chapter13.Section09.Marking
