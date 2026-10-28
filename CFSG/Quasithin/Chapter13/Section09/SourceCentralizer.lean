module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.Source
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Source

/-!
# The centralizer structure with source growth discharged

This literal application combines 13.9.5 with 13.9.8 on the original marked
configuration. Normality, the quotient model, B-normality, the two-core and
solvability all follow from the original simple QTKE hypotheses alone.
Source: Aschbacher--Smith, 13.9.5 and 13.9.8, printed pp.970--972.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The original 13.9.8 centralizer conclusions without an extra growth premise. -/
theorem source_centralizer_structure {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (d : Configuration G) (m : Marking d) :
    let C := centralizer ({m.z} : Set G)
    let N := m.core.subgroupOf C
    letI : N.Normal := m.marked_core_normal (hG.evenCharacteristic d.T)
    N.Normal ∧ Nonempty ((C ⧸ N) ≃* (Equiv.Perm (Fin 3) × BinaryFourPlus.C2)) ∧
      (m.B.subgroupOf C).Normal ∧ C ≤ normalizer (m.B : Set G) ∧
      C.pCoreIn 2 = m.B ⊔ m.core ∧ Group.IsSolvable C :=
  source13_9_8 hG d m (m.centralizer_growth hG).1

end CFSG.Quasithin.Chapter13.Section09
